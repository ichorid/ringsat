#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
// State variables for sigint_handler                                                                                                                                                                                                        
extern int no_sigint;
int no_sigint = 1;
extern int interrupts;
int interrupts = 0;
/* Catches signal interrupts from Ctrl+c.
If 1 signal is detected the simulation finishes the current frame and exits in a clean state. If Ctrl+c is pressed again it terminates the application without completing writes to files or calc
ulations but deallocates all memory anyway.
*/
void sigint_handler (int sig)
{
  if (sig == SIGINT)
    {
      interrupts += 1;
      std::cout << std::endl << "Aborting loop.. finishing frame." << std::endl;
      no_sigint = 0;

      if (interrupts>=2)
      {
        std::cerr << std::endl << "Multiple Interrupts issued: Clearing memory and Forcing immediate shutdown!" << std::endl;
        free_mem(); // write a function to free dynamycally allocated memory
        int devCount;
        cudaGetDeviceCount(&devCount);
        for (int i=0;i<devCount;++i) {cudaSetDevice(i); cudaResetDevice();}
        exit(9);
      }
    }
}
