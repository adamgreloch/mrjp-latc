@dnl = internal constant [4 x i8] c"%d\0A\00"
@d   = internal constant [3 x i8] c"%d\00"	
@re   = internal constant [15 x i8] c"runtime error\0A\00"	

declare i32 @printf(i8*, ...) 
declare i32 @scanf(i8*, ...)
declare i32 @puts(i8*)
declare void @exit(i32)
declare i32 @strcmp(i8*, i8*)

define void @printInt(i32 %x) {
  %t0 = getelementptr [4 x i8], [4 x i8]* @dnl, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
  ret void
}

define void @printString(i8* %s) {
  call i32 @puts(i8* %s)
	ret void
}

define void @error() {
  %t0 = getelementptr [15 x i8], [15 x i8]* @re, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  call void @exit(i32 1)
	ret void
}

define i32 @readInt() {
  %res = alloca i32
  %t1 = getelementptr [3 x i8], [3 x i8]* @d, i32 0, i32 0
	call i32 (i8*, ...) @scanf(i8* %t1, i32* %res)
	%t2 = load i32, i32* %res
	ret i32 %t2
}

define i1 @strEq(i8* %s1, i8* %s2) {
	%t1 = call i32 (i8*, i8*) @strcmp(i8* %s1, i8* %s2)
  %t2 = icmp eq i32 %t1, 0
	ret i1 %t2
}
