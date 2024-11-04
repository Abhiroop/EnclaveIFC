/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (C) 2006-2015, ARM Limited, All Rights Reserved
 *               2020, Intel Labs
 */

/*
 * SSL server demonstration program (with RA-TLS)
 * This program is originally based on an mbedTLS example ssl_server.c but uses RA-TLS flows (SGX
 * Remote Attestation flows) if RA-TLS library is required by user.
 * Note that this program builds against mbedTLS 3.x.
 */

#define _GNU_SOURCE
#include "mbedtls/build_info.h"

#include <assert.h>
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>
#include <sys/prctl.h>

#define mbedtls_fprintf fprintf
#define mbedtls_printf printf

#include "mbedtls/ctr_drbg.h"
#include "mbedtls/debug.h"
#include "mbedtls/entropy.h"
#include "mbedtls/error.h"
#include "mbedtls/net_sockets.h"
#include "mbedtls/ssl.h"
#include "mbedtls/x509.h"

/* RA-TLS: on server, only need ra_tls_create_key_and_crt_der() to create keypair and X.509 cert */
int (*ra_tls_create_key_and_crt_der_f)(uint8_t** der_key, size_t* der_key_size, uint8_t** der_crt,
                                       size_t* der_crt_size);

#define HTTP_RESPONSE                                    \
    "HTTP/1.0 200 OK\r\nContent-Type: text/html\r\n\r\n" \
    "<h2>mbed TLS Test Server</h2>\r\n"                  \
    "<p>Successful connection using: %s</p>\r\n"

#define DEBUG_LEVEL 0

#define MALICIOUS_STR "MALICIOUS DATA"

#define CA_CRT_PATH "ssl/ca.crt"
#define SRV_CRT_PATH "ssl/server.crt"
#define SRV_KEY_PATH "ssl/server.key"

#define MAX_EVT_LENGTH 256

static void my_debug(void* ctx, int level, const char* file, int line, const char* str) {
    ((void)level);

    mbedtls_fprintf((FILE*)ctx, "%s:%04d: %s\n", file, line, str);
    fflush((FILE*)ctx);
}

static ssize_t file_read(const char* path, char* buf, size_t count) {
    FILE* f = fopen(path, "r");
    if (!f)
        return -errno;

    ssize_t bytes = fread(buf, 1, count, f);
    if (bytes <= 0) {
        int errsv = errno;
        fclose(f);
        return -errsv;
    }

    int close_ret = fclose(f);
    if (close_ret < 0)
        return -errno;

    return bytes;
}


int enforcer_shim(const char *input) {
    char buffer[256];
    char temp_filename[] = "/tmp/temp_input_XXXXXX";
    FILE *temp_file;
    int fd;

    // Create a temporary file for input
    fd = mkstemp(temp_filename);
    if (fd == -1) {
        perror("mkstemp");
        exit(EXIT_FAILURE);
    }

    // Write the input to the temporary file
    temp_file = fdopen(fd, "w");
    if (temp_file == NULL) {
        perror("fdopen");
        close(fd);
        exit(EXIT_FAILURE);
    }
    fprintf(temp_file, "%s", input);
    fclose(temp_file);

    // Construct the command to read from the temporary file
    char command[512];
    snprintf(command, sizeof(command), "enforcer/whyenf.exe -sig enforcer/covid.sig -formula enforcer/covid_output.mfotl < %s", temp_filename);

    // Use popen to run the command and read its output
    FILE *pipe = popen(command, "r");
    if (pipe == NULL) {
        perror("popen");
        unlink(temp_filename);  // Clean up the temporary file
        exit(EXIT_FAILURE);
    }

    // Read and process the output from ./foo
    while (fgets(buffer, sizeof(buffer), pipe) != NULL) {
        printf("Output from executing whyenf: %s", buffer);
    }

    // XXX: return buffer here

    // Clean up
    pclose(pipe);
    unlink(temp_filename);  // Delete the temporary file

    return 0;
}

int startServer(int *flag, char *data) {

  // ABHI : Property-based Attestation setup begins

  /*
   * fork() a separate enclave 
   */
  int pipe1_TEE_Enf[2]; // Pipe 1: TEE --> Enforcer
  int pipe2_Enf_TEE[2]; // Pipe 2: Enforcer --> TEE
  pid_t pid;
  char TEE_msg[] = "Hello from TEE"; // will be the trace
  char Enf_msg[] = "Hello from Enforcer";  // enforcer action
  char read_buffer[200];

  // Create both pipes
  if (pipe(pipe1_TEE_Enf) == -1 || pipe(pipe2_Enf_TEE) == -1) {
    perror("Bidirectional channel creation error");
  }


  pid = fork(); // forks an OS-level process that is locally attested

  if (pid < 0) {  // Error during fork
    perror("Error forking Enclave process");
  }

  // ABHI : Property-based Attestation setup ends

  if(pid > 0) { // TEE process begins; else is the enforcer
    // Close unused ends of the pipes
    close(pipe1_TEE_Enf[0]);
    close(pipe2_Enf_TEE[1]);




    int ret;
    size_t len;
    mbedtls_net_context listen_fd;
    mbedtls_net_context client_fd;
    unsigned char buf[1024];
    const char* pers = "ssl_server";
    void* ra_tls_attest_lib;

    uint8_t* der_key = NULL;
    uint8_t* der_crt = NULL;

    mbedtls_entropy_context entropy;
    mbedtls_ctr_drbg_context ctr_drbg;
    mbedtls_ssl_context ssl;
    mbedtls_ssl_config conf;
    mbedtls_x509_crt srvcert;
    mbedtls_pk_context pkey;

    mbedtls_net_init(&listen_fd);
    mbedtls_net_init(&client_fd);
    mbedtls_ssl_init(&ssl);
    mbedtls_ssl_config_init(&conf);
    mbedtls_x509_crt_init(&srvcert);
    mbedtls_pk_init(&pkey);
    mbedtls_entropy_init(&entropy);
    mbedtls_ctr_drbg_init(&ctr_drbg);

#if defined(MBEDTLS_DEBUG_C)
    mbedtls_debug_set_threshold(DEBUG_LEVEL);
#endif


    // ABHI : ATTESTATION - Check if its EPID or DCAP; opens libra_tls_attest.so;
    // Populates ra_tls_create_key_and_crt_der_f from the library;

    char attestation_type_str[32] = {0};
    ret = file_read("/dev/attestation/attestation_type", attestation_type_str,
                    sizeof(attestation_type_str) - 1);
    if (ret < 0 && ret != -ENOENT) {
        mbedtls_printf("User requested RA-TLS attestation but cannot read SGX-specific file "
                       "/dev/attestation/attestation_type\n");
        return 1;
    }

    if (ret == -ENOENT || !strcmp(attestation_type_str, "none")) {
        ra_tls_attest_lib = NULL;
        ra_tls_create_key_and_crt_der_f = NULL;
    } else if (!strcmp(attestation_type_str, "epid") || !strcmp(attestation_type_str, "dcap")) {
        ra_tls_attest_lib = dlopen("libra_tls_attest.so", RTLD_LAZY);
        if (!ra_tls_attest_lib) {
            mbedtls_printf("User requested RA-TLS attestation but cannot find lib\n");
            return 1;
        }

        char* error;
        ra_tls_create_key_and_crt_der_f = dlsym(ra_tls_attest_lib, "ra_tls_create_key_and_crt_der");
        if ((error = dlerror()) != NULL) {
            mbedtls_printf("%s\n", error);
            return 1;
        }
    } else {
        mbedtls_printf("Unrecognized remote attestation type: %s\n", attestation_type_str);
        return 1;
    }


    // ABHI: SEED THE RNG

    mbedtls_printf("  . Seeding the random number generator...");
    fflush(stdout);

    ret = mbedtls_ctr_drbg_seed(&ctr_drbg, mbedtls_entropy_func, &entropy,
                                (const unsigned char*)pers, strlen(pers));
    if (ret != 0) {
        mbedtls_printf(" failed\n  ! mbedtls_ctr_drbg_seed returned %d\n", ret);
        goto exit;
    }

    mbedtls_printf(" ok\n");

    // ABHI : Load the certificates and private RSA Key
    // In this phase a lot of the logic of embedding the quote and report is handled
    // Most of that logic is in if(ra_tls_attest_lib){ ... } branch

    if (ra_tls_attest_lib) {
        mbedtls_printf("\n  . Creating the RA-TLS server cert and key (using \"%s\" as "
                       "attestation type)...", attestation_type_str);
        fflush(stdout);

        size_t der_key_size;
        size_t der_crt_size;

        ret = (*ra_tls_create_key_and_crt_der_f)(&der_key, &der_key_size, &der_crt, &der_crt_size);
        if (ret != 0) {
            mbedtls_printf(" failed\n  !  ra_tls_create_key_and_crt_der returned %d\n\n", ret);
            goto exit;
        }

        ret = mbedtls_x509_crt_parse(&srvcert, (unsigned char*)der_crt, der_crt_size);
        if (ret != 0) {
            mbedtls_printf(" failed\n  !  mbedtls_x509_crt_parse returned %d\n\n", ret);
            goto exit;
        }

        ret = mbedtls_pk_parse_key(&pkey, (unsigned char*)der_key, der_key_size, /*pwd=*/NULL, 0,
                                   mbedtls_ctr_drbg_random, &ctr_drbg);
        if (ret != 0) {
            mbedtls_printf(" failed\n  !  mbedtls_pk_parse_key returned %d\n\n", ret);
            goto exit;
        }

        mbedtls_printf(" ok\n");

        /* if (argc > 1) { */
        /*     /\* user asks to maliciously modify the embedded SGX quote (for testing purposes) *\/ */
        /*     mbedtls_printf("  . Maliciously modifying SGX quote embedded in RA-TLS cert..."); */
        /*     fflush(stdout); */

        /*     uint8_t oid[] = {0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF8, 0x4D, 0x8A, 0x39, 0x06}; */
        /*     uint8_t* p = memmem(srvcert.v3_ext.p, srvcert.v3_ext.len, oid, sizeof(oid)); */
        /*     if (!p) { */
        /*         mbedtls_printf(" failed\n  !  No embedded SGX quote found\n\n"); */
        /*         goto exit; */
        /*     } */

        /*     p += sizeof(oid); */
        /*     p += 5; /\* jump somewhere in the middle of the SGX quote *\/ */
        /*     if (p + sizeof(MALICIOUS_STR) > srvcert.v3_ext.p + srvcert.v3_ext.len) { */
        /*         mbedtls_printf(" failed\n  !  Size of embedded SGX quote is too small\n\n"); */
        /*         goto exit; */
        /*     } */

        /*     memcpy(p, MALICIOUS_STR, sizeof(MALICIOUS_STR)); */
        /*     mbedtls_printf(" ok\n"); */
        /* } */
    } else {
        mbedtls_printf("\n  . Creating normal server cert and key...");
        fflush(stdout);

        ret = mbedtls_x509_crt_parse_file(&srvcert, SRV_CRT_PATH);
        if (ret != 0) {
            mbedtls_printf(" failed\n  !  mbedtls_x509_crt_parse_file returned %d\n\n", ret);
            goto exit;
        }

        ret = mbedtls_x509_crt_parse_file(&srvcert, CA_CRT_PATH);
        if (ret != 0) {
            mbedtls_printf(" failed\n  !  mbedtls_x509_crt_parse_file returned %d\n\n", ret);
            goto exit;
        }

        ret = mbedtls_pk_parse_keyfile(&pkey, SRV_KEY_PATH, /*password=*/NULL,
                                       mbedtls_ctr_drbg_random, &ctr_drbg);
        if (ret != 0) {
            mbedtls_printf(" failed\n  !  mbedtls_pk_parse_keyfile returned %d\n\n", ret);
            goto exit;
        }

        mbedtls_printf(" ok\n");
    }

    // ABHI : Setup the listening socket

    mbedtls_printf("  . Bind on https://localhost:4433/ ...");
    fflush(stdout);

    ret = mbedtls_net_bind(&listen_fd, NULL, "4433", MBEDTLS_NET_PROTO_TCP);
    if (ret != 0) {
        mbedtls_printf(" failed\n  ! mbedtls_net_bind returned %d\n\n", ret);
        goto exit;
    }

    mbedtls_printf(" ok\n");

    // ABHI : Setup stuff

    mbedtls_printf("  . Setting up the SSL data....");
    fflush(stdout);

    ret = mbedtls_ssl_config_defaults(&conf, MBEDTLS_SSL_IS_SERVER, MBEDTLS_SSL_TRANSPORT_STREAM,
                                      MBEDTLS_SSL_PRESET_DEFAULT);
    if (ret != 0) {
        mbedtls_printf(" failed\n  ! mbedtls_ssl_config_defaults returned %d\n\n", ret);
        goto exit;
    }

    mbedtls_ssl_conf_rng(&conf, mbedtls_ctr_drbg_random, &ctr_drbg);
    mbedtls_ssl_conf_dbg(&conf, my_debug, stdout);

    if (!ra_tls_attest_lib) {
        /* no RA-TLS attest library present, use embedded CA chain */
        mbedtls_ssl_conf_ca_chain(&conf, srvcert.next, NULL);
    }

    ret = mbedtls_ssl_conf_own_cert(&conf, &srvcert, &pkey);
    if (ret != 0) {
        mbedtls_printf(" failed\n  ! mbedtls_ssl_conf_own_cert returned %d\n\n", ret);
        goto exit;
    }

    ret = mbedtls_ssl_setup(&ssl, &conf);
    if (ret != 0) {
        mbedtls_printf(" failed\n  ! mbedtls_ssl_setup returned %d\n\n", ret);
        goto exit;
    }

    mbedtls_printf(" ok\n");

reset:
#ifdef MBEDTLS_ERROR_C
    if (ret != 0) {
        char error_buf[100];
        mbedtls_strerror(ret, error_buf, sizeof(error_buf));
        mbedtls_printf("Last error was: %d - %s\n\n", ret, error_buf);
    }
#endif

    mbedtls_net_free(&client_fd);

    mbedtls_ssl_session_reset(&ssl);

    //ABHI : wait until a client connects

    mbedtls_printf("  . Waiting for a remote connection ...");
    fflush(stdout);

    ret = mbedtls_net_accept(&listen_fd, &client_fd, NULL, 0, NULL);
    if (ret != 0) {
        mbedtls_printf(" failed\n  ! mbedtls_net_accept returned %d\n\n", ret);
        goto exit;
    }

    mbedtls_ssl_set_bio(&ssl, &client_fd, mbedtls_net_send, mbedtls_net_recv, NULL);

    mbedtls_printf(" ok\n");

    //ABHI: Handshake

    mbedtls_printf("  . Performing the SSL/TLS handshake...");
    fflush(stdout);

    while ((ret = mbedtls_ssl_handshake(&ssl)) != 0) {
        if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
            mbedtls_printf(" failed\n  ! mbedtls_ssl_handshake returned %d\n\n", ret);
            goto reset;
        }
    }

    mbedtls_printf(" ok\n");

    // ABHI: Read the HTTP Request

    mbedtls_printf("  < Read from client:");
    fflush(stdout);

    do {
        len = sizeof(buf) - 1;
        memset(buf, 0, sizeof(buf));
        ret = mbedtls_ssl_read(&ssl, buf, len);

        if (ret == MBEDTLS_ERR_SSL_WANT_READ || ret == MBEDTLS_ERR_SSL_WANT_WRITE)
            continue;

        if (ret <= 0) {
            switch (ret) {
                case MBEDTLS_ERR_SSL_PEER_CLOSE_NOTIFY:
                    mbedtls_printf(" connection was closed gracefully\n");
                    break;

                case MBEDTLS_ERR_NET_CONN_RESET:
                    mbedtls_printf(" connection was reset by peer\n");
                    break;

                default:
                    mbedtls_printf(" mbedtls_ssl_read returned -0x%x\n", -ret);
                    break;
            }

            break;
        }

        len = ret;
        mbedtls_printf(" %lu bytes read\n\n%s", len, (char*)buf);

        if (ret > 0)
            break;
    } while (1);


    // ABHI: Data is received and is now in buf

    memcpy(data, buf, len);// Copying the data so that Haskell can read it

    *flag = 1;
    // Haskell Thread operational now
    unsigned int milliseconds = 200; // 200 milliseconds

    while(*flag == 1){
      usleep(milliseconds * 1000);
    }


    //Haskell has reset data
    size_t size = 0;
    for (int i = 0; i < sizeof(size_t); i++) {
      size = (size << 8) | (uint8_t)data[i];
    }
    len = sizeof(size_t) + size;

    memcpy(buf, data, len); // buf will be written back to client

    // ABHI : Before writing back to client attest behaviour

    // NOTE This is a post-action check; after the enclave has taken
    // the desired action we consult the enforcer; we can kill the
    // enclave after the enforcer says some action `A` produced a bad trace
    // but by now atleast one bad action (A) could have corrupted
    // the state (especially if this is persistent state)

    // Also, NOTE the enforcer and the server loop are synchronous and
    // a bad enforcer may block the server loop, which is bad for perf.

    ssize_t bytesWritten;
    ssize_t bytesRead;

    mbedtls_printf("f(data) computed!");

    // Write the trace to the enforcer through Pipe 1
    /* Parse the last event */
    const char *logFile = "calltrace.log"; //XXX: check if sealing key can be shared between enclaves

    FILE *file = fopen(logFile, "r");
    if (file == NULL) {
      perror("Error opening file");
    }

    char line[MAX_EVT_LENGTH];
    char last_line[MAX_EVT_LENGTH] = "";

    // Read each line and store it in last_line
    while (fgets(line, sizeof(line), file) != NULL) {
      strncpy(last_line, line, MAX_EVT_LENGTH - 1);
      last_line[MAX_EVT_LENGTH - 1] = '\0'; // Ensure null termination
    }

    fclose(file);

    // last_line should be fed to enforcer through the pipe
    // XXX: Major problem: the output is computed as a list and then the log is interspersed so
    //      parsing the last event is incorrect because you want to capture all of the output events
    // HACK: Parse log and read bring all events which has the same timestamp;
    /*
     * will lead to redundant enforcement computation like:
       @10 foo(1)
       @10 foo(2)
       @10 foo(3)
       @20 foo(4)

       so, as the log is written, we will consult with the enforcer for `foo(1)`, `foo(1), foo(2)`,
       `foo(1),foo(2),foo(3)`. Maybe there is a scope for optimisation here, where we consult the
       enforcer as a bulk call.
     */

    bytesWritten = write(pipe1_TEE_Enf[1], last_line, strlen(last_line) + 1); // +1 for null terminator

    if (bytesWritten == -1) {
      perror("Write to enforcer failed");
    }

    // Read the response from the enforcer through Pipe 2
    bytesRead = read(pipe2_Enf_TEE[0], read_buffer, sizeof(read_buffer));
    if (bytesRead == -1) {
      perror("Read from enforcer failed");
    }
    mbedtls_printf("  . TEE received: %s\n\n\n", read_buffer);

    // We can read from `read_buffer` and depending on what the enforcer wants, we can terminate the enclave

    // ABHI: Behaviour attested now write back to client



    mbedtls_printf("  > Write to client:");
    fflush(stdout);

    //len = sprintf((char*)buf, HTTP_RESPONSE, mbedtls_ssl_get_ciphersuite(&ssl)); //XXX: Abhi: writing the HTTP response here

    while ((ret = mbedtls_ssl_write(&ssl, buf, len)) <= 0) {
        if (ret == MBEDTLS_ERR_NET_CONN_RESET) {
            mbedtls_printf(" failed\n  ! peer closed the connection\n\n");
            goto reset;
        }

        if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
            mbedtls_printf(" failed\n  ! mbedtls_ssl_write returned %d\n\n", ret);
            goto exit;
        }
    }

    len = ret;
    mbedtls_printf(" %lu bytes written\n\n%s\n", len, (char*)buf);

    mbedtls_printf("  . Closing the connection...");

    while ((ret = mbedtls_ssl_close_notify(&ssl)) < 0) {
        if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
            mbedtls_printf(" failed\n  ! mbedtls_ssl_close_notify returned %d\n\n", ret);
            goto reset;
        }
    }

    mbedtls_printf(" ok\n");

    ret = 0;
    goto reset; // ABHI: recursion and loop the server

exit:
#ifdef MBEDTLS_ERROR_C
    if (ret != 0) {
        char error_buf[100];
        mbedtls_strerror(ret, error_buf, sizeof(error_buf));
        mbedtls_printf("Last error was: %d - %s\n\n", ret, error_buf);
    }
#endif

    if (ra_tls_attest_lib)
        dlclose(ra_tls_attest_lib);

    mbedtls_net_free(&client_fd);
    mbedtls_net_free(&listen_fd);

    mbedtls_x509_crt_free(&srvcert);
    mbedtls_pk_free(&pkey);
    mbedtls_ssl_free(&ssl);
    mbedtls_ssl_config_free(&conf);
    mbedtls_ctr_drbg_free(&ctr_drbg);
    mbedtls_entropy_free(&entropy);

    free(der_key);
    free(der_crt);


    // Close the used ends after communication (from the PBA channel)
    close(pipe1_TEE_Enf[1]);
    close(pipe2_Enf_TEE[0]);


    return ret;
  } else if (pid == 0) { // Enforcer process


    //XXX: Do we really want the Enforcer to die when the TEE dies?
    //     Can the TEE misuse this power to bypass the enforcer?
    // Set enforcer to terminate when TEE(parent) dies
    prctl(PR_SET_PDEATHSIG, SIGTERM);

    // Verify that parent(TEE) is alive at the time of setting up PR_SET_PDEATHSIG
    if (getppid() == 1) {
      printf("Parent has already exited.\n");
      exit(1);
    }

    // Close unused ends of the pipes
    close(pipe1_TEE_Enf[1]);
    close(pipe2_Enf_TEE[0]);


    //read_buffer holds the trace
    /*
      while(1){
      read // blocks and change context (hopefully)
      read_buffer holds the trace
      call enf_action = enforcer(trace)
      write(enf_action) to enclave
      }
    */


    while(1){
      ssize_t bytesWritten;
      ssize_t bytesRead;


      // Read the message from the TEE through Pipe 1
      bytesRead = read(pipe1_TEE_Enf[0], read_buffer, sizeof(read_buffer));
      if (bytesRead == -1) {
        perror("Read from TEE failed");
      }

      mbedtls_printf("  . Enforcer received: %s\n", read_buffer);

      // Call whyenf on the trace from read_buffer

      enforcer_shim(read_buffer);

      // Done executing


      // Send a response to the TEE through Pipe 2
      bytesWritten = write(pipe2_Enf_TEE[1], Enf_msg, strlen(Enf_msg) + 1); // +1 for null terminator
      if (bytesWritten == -1) {
        perror("Write to TEE failed");
      }
    }

    // Close the used ends after communication
    close(pipe1_TEE_Enf[0]);
    close(pipe2_Enf_TEE[1]);
    return 0;

  }
}
