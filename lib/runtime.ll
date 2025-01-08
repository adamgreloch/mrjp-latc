%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, %struct._IO_codecvt*, %struct._IO_wide_data*, %struct._IO_FILE*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type opaque
%struct._IO_codecvt = type opaque
%struct._IO_wide_data = type opaque

@stdin = external dso_local global %struct._IO_FILE*, align 8

@snl = internal constant [4 x i8] c"%s\0A\00"
@dnl = internal constant [4 x i8] c"%d\0A\00"
@d   = internal constant [3 x i8] c"%d\00"	
@re   = internal constant [15 x i8] c"runtime error\0A\00"	

declare i32 @printf(i8*, ...) 
declare i32 @scanf(i8*, ...)
declare i32 @puts(i8*)
declare void @exit(i32)
declare i32 @strcmp(i8*, i8*)
declare i8* @strncat(i8*, i8*, i32)
declare i32 @strlen(i8*)
declare i8* @malloc(i32)
declare i64 @getline(i8**, i64*, %struct._IO_FILE*)
declare i8* @memcpy(i8*, i8*, i32)

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

define i8* @readString() {
  %t1 = alloca i8*, align 8
  %t2 = alloca i64, align 8
  store i8* null, i8** %t1, align 8
  %t3 = load %struct._IO_FILE*, %struct._IO_FILE** @stdin, align 8
  %t4 = call i64 @getline(i8** %t1, i64* %t2, %struct._IO_FILE* %t3)
  %t5 = icmp eq i64 %t4, -1
  br i1 %t5, label %L0, label %L1
L0:
  call void @exit(i32 noundef 1) #4
  unreachable
L1:
  %t8 = load i8*, i8** %t1, align 8
  ret i8* %t8
}

define i8* @concatStrings(i8* %s1, i8* %s2) {
  %len1 = call i32 @strlen(i8* %s1)
  %l1 = add i32 %len1, 1
  %len2 = call i32 @strlen(i8* %s1)
  %t0 = add i32 %len1, %len2
  %t1 = add i32 %t0, 1

  %buf = call i8* @malloc(i32 %t1)
  call i8* @memcpy(i8* %buf, i8* %s1, i32 %l1)

  %res = call i8* @strncat(i8* %buf, i8* %s2, i32 %t1)
	ret i8* %res
}
