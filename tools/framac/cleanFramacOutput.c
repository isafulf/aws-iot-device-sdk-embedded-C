#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

int main(int argc, char **argv)
{
    printf("here 0");

    FILE *stream;
    char *function = argv[1];
    char *line = NULL;
    size_t len = 0;
    ssize_t read;

    stream = fopen(argv[2], "r");
    if (stream == NULL)
    exit(EXIT_FAILURE);

    bool firstDashLine = false;
    bool start = false;
    char * functionStart = "--- Properties of Function '";
    strcat(functionStart, function);

    printf("here 1");
    while ((read = getline(&line, &len, stream)) != -1) {
        if (!firstDashLine) {
            if(strstr(line, "--------------------------------------------------------------------------------") != NULL) {
                firstDashLine = true;
            } else {
                printf(line);
            }
        } else {
            if(strstr(line, functionStart) != NULL) {
                printf("--------------------------------------------------------------------------------");
                bool start = true;
            } else if(start == true) {
                if(strstr(line, "--------------------------------------------------------------------------------") != NULL) {
                    break;
                } 
                printf(line);

            }

        }
    }

    free(line);
    fclose(stream);
    exit(EXIT_SUCCESS);
}

