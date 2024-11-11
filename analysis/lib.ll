; ModuleID = 'lib.ad118e182f7a4706-cgu.0'
source_filename = "lib.ad118e182f7a4706-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
define void @analysis(ptr dead_on_unwind noalias nocapture noundef writable writeonly sret([40 x i8]) align 8 dereferenceable(40) %_0, ptr noalias noundef nonnull readonly align 1 %bytes.0, i64 noundef %bytes.1) unnamed_addr #0 personality ptr @rust_eh_personality {
bb3.i:
  %0 = icmp eq i64 %bytes.1, 0
  br i1 %0, label %"_ZN3lib17Peekable$LT$T$GT$7next_if17ha871c0d4b20cf51bE.exit", label %bb6.i

bb6.i:                                            ; preds = %bb3.i
  %_24.i.i = getelementptr inbounds i8, ptr %bytes.0, i64 1
  %_4.i.i = load i8, ptr %bytes.0, align 1, !noalias !3, !noundef !8
  %_0.i.i = icmp ne i8 %_4.i.i, 69
  %spec.select1 = zext i1 %_0.i.i to i64
  br label %"_ZN3lib17Peekable$LT$T$GT$7next_if17ha871c0d4b20cf51bE.exit"

"_ZN3lib17Peekable$LT$T$GT$7next_if17ha871c0d4b20cf51bE.exit": ; preds = %bb6.i, %bb3.i
  %iter.sroa.12.0 = phi ptr [ null, %bb3.i ], [ %bytes.0, %bb6.i ]
  %iter.sroa.14.1 = phi ptr [ %bytes.0, %bb3.i ], [ %_24.i.i, %bb6.i ]
  %iter.sroa.0.0 = phi i64 [ 1, %bb3.i ], [ %spec.select1, %bb6.i ]
  %_9 = getelementptr inbounds i8, ptr %bytes.0, i64 %bytes.1
  store i64 %iter.sroa.0.0, ptr %_0, align 8
  %iter.sroa.12.0._0.sroa_idx = getelementptr inbounds i8, ptr %_0, i64 16
  store ptr %iter.sroa.12.0, ptr %iter.sroa.12.0._0.sroa_idx, align 8
  %iter.sroa.14.0._0.sroa_idx = getelementptr inbounds i8, ptr %_0, i64 24
  store ptr %iter.sroa.14.1, ptr %iter.sroa.14.0._0.sroa_idx, align 8
  %iter.sroa.17.0._0.sroa_idx = getelementptr inbounds i8, ptr %_0, i64 32
  store ptr %_9, ptr %iter.sroa.17.0._0.sroa_idx, align 8
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
!3 = !{!4, !6}
!4 = distinct !{!4, !5, !"_ZN3lib8analysis28_$u7b$$u7b$closure$u7d$$u7d$17hb9877fe35f799b62E: %x"}
!5 = distinct !{!5, !"_ZN3lib8analysis28_$u7b$$u7b$closure$u7d$$u7d$17hb9877fe35f799b62E"}
!6 = distinct !{!6, !7, !"_ZN3lib17Peekable$LT$T$GT$7next_if17ha871c0d4b20cf51bE: %self"}
!7 = distinct !{!7, !"_ZN3lib17Peekable$LT$T$GT$7next_if17ha871c0d4b20cf51bE"}
!8 = !{}
