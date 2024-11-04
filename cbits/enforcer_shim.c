#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>


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
    snprintf(command, sizeof(command), "../enforcer/whyenf.exe -sig ../enforcer/covid.sig -formula ../enforcer/covid_output.mfotl < %s", temp_filename);

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

    // return buffer here

    // Clean up
    pclose(pipe);
    unlink(temp_filename);  // Delete the temporary file
    return 0;
}

int main() {
	const char *input = "@1730736222     input(\"client1\",77,\"XBB15\")";
	enforcer_shim(input);
}	

