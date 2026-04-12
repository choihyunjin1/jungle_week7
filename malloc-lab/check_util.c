// Quick utility to compute exact util values
#include <stdio.h>

int main() {
    double utils[] = {0.99, 1.00, 0.99, 1.00, 0.99, 0.96, 0.94, 0.97, 0.90, 1.00, 1.00};
    int n = 11;
    double sum = 0;
    for (int i = 0; i < n; i++) sum += utils[i];
    double avg = sum / n;
    double p1 = 0.60 * avg;
    double p2 = 0.40;
    double perfindex = (p1 + p2) * 100.0;
    
    printf("Sum util = %.4f\n", sum);
    printf("Avg util = %.6f (%.2f%%)\n", avg, avg*100);
    printf("p1 = %.6f\n", p1);
    printf("p2 = %.6f\n", p2);
    printf("perfindex = %.2f\n", perfindex);
    printf("Need perfindex >= 99.5 for 100/100\n");
    printf("Need avg_util >= %.6f (%.2f%%)\n", 0.995/0.6, 0.995*100/0.6);
    
    // What if binary2 goes to 91%?
    utils[8] = 0.91;
    sum = 0;
    for (int i = 0; i < n; i++) sum += utils[i];
    avg = sum / n;
    perfindex = (0.6*avg + 0.4) * 100;
    printf("\nWith binary2=91%%: avg=%.4f%%, perf=%.2f\n", avg*100, perfindex);
    
    // What if binary2 goes to 95%?
    utils[8] = 0.95;
    sum = 0;
    for (int i = 0; i < n; i++) sum += utils[i];
    avg = sum / n;
    perfindex = (0.6*avg + 0.4) * 100;
    printf("With binary2=95%%: avg=%.4f%%, perf=%.2f\n", avg*100, perfindex);
    
    // What we need from binary2 alone?
    double target_sum = 0.99167 * 11;
    double needed_binary2 = target_sum - (sum - 0.95);
    printf("\nNeed binary2 >= %.4f (%.2f%%) if others unchanged\n", needed_binary2, needed_binary2*100);
    
    return 0;
}
