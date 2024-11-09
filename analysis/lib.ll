; ModuleID = 'lib.ad118e182f7a4706-cgu.0'
source_filename = "lib.ad118e182f7a4706-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @do_it(ptr dead_on_unwind noalias nocapture noundef writable writeonly sret([40 x i8]) align 8 dereferenceable(40) %_0, ptr noalias noundef nonnull readonly align 1 %thing.0, i64 noundef %thing.1) unnamed_addr #0 personality ptr @rust_eh_personality {
bb3.i:
  %0 = icmp eq i64 %thing.1, 0
  br i1 %0, label %"_ZN3lib17Peekable$LT$T$GT$7next_if17hf28c2ba6859b63f7E.exit", label %bb6.i

bb6.i:                                            ; preds = %bb3.i
  %_24.i.i = getelementptr inbounds i8, ptr %thing.0, i64 1
  %_4.i.i = load i8, ptr %thing.0, align 1, !noalias !3, !noundef !3
  %_0.i.i = icmp eq i8 %_4.i.i, 69
  br i1 %_0.i.i, label %bb3.i18, label %"_ZN3lib17Peekable$LT$T$GT$7next_if17hf28c2ba6859b63f7E.exit"

bb3.i18:                                          ; preds = %bb6.i
  %1 = icmp eq i64 %thing.1, 1
  br i1 %1, label %"_ZN3lib17Peekable$LT$T$GT$7next_if17hf28c2ba6859b63f7E.exit", label %bb6.i22

bb6.i22:                                          ; preds = %bb3.i18
  %_24.i.i23 = getelementptr inbounds i8, ptr %thing.0, i64 2
  %_4.i.i24 = load i8, ptr %_24.i.i, align 1, !noalias !4, !noundef !3
  %_0.i.i25 = icmp ne i8 %_4.i.i24, 69
  %spec.select = select i1 %_0.i.i25, ptr %_24.i.i, ptr undef
  %2 = zext i1 %_0.i.i25 to i64
  br label %"_ZN3lib17Peekable$LT$T$GT$7next_if17hf28c2ba6859b63f7E.exit"

"_ZN3lib17Peekable$LT$T$GT$7next_if17hf28c2ba6859b63f7E.exit": ; preds = %bb6.i, %bb3.i, %bb6.i22, %bb3.i18
  %peeking.sroa.19.1 = phi ptr [ null, %bb3.i18 ], [ %spec.select, %bb6.i22 ], [ null, %bb3.i ], [ %thing.0, %bb6.i ]
  %peeking.sroa.23.3 = phi ptr [ %_24.i.i, %bb3.i18 ], [ %_24.i.i23, %bb6.i22 ], [ %thing.0, %bb3.i ], [ %_24.i.i, %bb6.i ]
  %peeking.sroa.0.1.shrunk = phi i64 [ 1, %bb3.i18 ], [ %2, %bb6.i22 ], [ 1, %bb3.i ], [ 1, %bb6.i ]
  %_11 = getelementptr inbounds i8, ptr %thing.0, i64 %thing.1
  store i64 %peeking.sroa.0.1.shrunk, ptr %_0, align 8
  %peeking.sroa.19.0._0.sroa_idx = getelementptr inbounds i8, ptr %_0, i64 16
  store ptr %peeking.sroa.19.1, ptr %peeking.sroa.19.0._0.sroa_idx, align 8
  %peeking.sroa.23.0._0.sroa_idx = getelementptr inbounds i8, ptr %_0, i64 24
  store ptr %peeking.sroa.23.3, ptr %peeking.sroa.23.0._0.sroa_idx, align 8
  %peeking.sroa.28.0._0.sroa_idx = getelementptr inbounds i8, ptr %_0, i64 32
  store ptr %_11, ptr %peeking.sroa.28.0._0.sroa_idx, align 8
  ret void
}

; Function Attrs: nounwind nonlazybind uwtable
declare noundef i32 @rust_eh_personality(i32 noundef, i32 noundef, i64 noundef, ptr noundef, ptr noundef) unnamed_addr #1

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.81.0 (eeb90cda1 2024-09-04)"}
!3 = !{}
!4 = !{!5, !7}
!5 = distinct !{!5, !6, !"_ZN3lib5do_it28_$u7b$$u7b$closure$u7d$$u7d$17hf8f4dcccd8c63e60E: %thing"}
!6 = distinct !{!6, !"_ZN3lib5do_it28_$u7b$$u7b$closure$u7d$$u7d$17hf8f4dcccd8c63e60E"}
!7 = distinct !{!7, !8, !"_ZN3lib17Peekable$LT$T$GT$7next_if17hf28c2ba6859b63f7E: %self"}
!8 = distinct !{!8, !"_ZN3lib17Peekable$LT$T$GT$7next_if17hf28c2ba6859b63f7E"}
