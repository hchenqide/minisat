files:
- ./cnfuzz.c
- ./drup-trim.c (exit return values modified)
- ./minisat (folder)
- ./test/fuzz.cc

build:
- gcc cnfuzz.c -O2 -o ./build/cnfuzz
- gcc drup-trim.c -O2 -o ./build/drup-trim
- cd ./build; cmake ..; make; cd ..

fuzz:
- ./run_fuzz.sh ./build/cnfuzz ./build/fuzz ./build/drup-trim


extra: (drup-trim diff)
```
--- drup-trim.c	2025-01-11 17:26:17.189578400 +0100
+++ drup-trim-updated.c	2025-01-11 17:22:13.102403600 +0100
@@ -255,7 +255,7 @@
       struct timeval current_time;
       gettimeofday(&current_time, NULL);
       int seconds = (int) (current_time.tv_sec - S->start_time.tv_sec);
-      if (seconds > S->timeout) printf("s TIMEOUT\n"), exit(0);
+      if (seconds > S->timeout) printf("s TIMEOUT\n"), exit(1);
 
       if (S->traceFile) {
         fprintf(S->traceFile, "%lu ", S->time >> 1);
@@ -365,7 +365,7 @@
   printf("c error: could not match deleted clause ");
   for (i = 0; i < size; ++i) printf("%i ", input[i]);
   printf("\ns MATCHING ERROR\n");
-  exit(0);
+  exit(1);
   return 0;
 }
 
@@ -446,7 +446,7 @@
       else tmp = fscanf (S->proofFile, " %i ", &lit);
       if (tmp == EOF && !fileSwitchFlag) fileSwitchFlag = 1; }
     if (tmp == EOF && fileSwitchFlag) break;
-    if (abs(lit) > n) { printf("c illegal literal %i due to max var %i\n", lit, n); exit(0); }
+    if (abs(lit) > n) { printf("c illegal literal %i due to max var %i\n", lit, n); exit(1); }
     if (!lit) {
       unsigned int hash = getHash (marks, ++mark, buffer, size);
       if (del) {
@@ -576,7 +576,7 @@
   fclose (S.proofFile);
   int sts = ERROR;
   if       (parseReturnValue == ERROR) printf("s MEMORY ALLOCATION ERROR\n");
-  else if  (parseReturnValue == UNSAT) printf("s TRIVIAL UNSAT\n");
+  else if  (parseReturnValue == UNSAT) sts = UNSAT, printf("s TRIVIAL UNSAT\n");
   else if  ((sts = verify (&S)) == UNSAT) printf("s VERIFIED\n");
   else printf("s NOT VERIFIED\n")  ;
   freeMemory(&S);
```
