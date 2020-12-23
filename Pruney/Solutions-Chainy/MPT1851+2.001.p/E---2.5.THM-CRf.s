%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   96 (2032 expanded)
%              Number of clauses        :   63 ( 781 expanded)
%              Number of leaves         :   16 ( 501 expanded)
%              Depth                    :   18
%              Number of atoms          :  310 (7595 expanded)
%              Number of equality atoms :   23 ( 936 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v2_tdlat_3(X1) )
           => v2_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t58_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
      <=> u1_pre_topc(X1) = k2_tarski(k1_xboole_0,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(t78_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(t35_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v1_tops_2(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                   => ( X4 = X2
                     => v1_tops_2(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(t31_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v2_tdlat_3(X1) )
             => v2_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_tex_2])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))
      | m1_pre_topc(X13,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & v2_tdlat_3(esk1_0)
    & ~ v2_tdlat_3(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X14,X15] :
      ( ( ~ m1_pre_topc(X14,X15)
        | m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))
        | m1_pre_topc(X14,X15)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_22,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r1_tarski(u1_struct_0(X27),u1_struct_0(X28))
        | m1_pre_topc(X27,X28)
        | ~ m1_pre_topc(X28,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_pre_topc(X27,X28)
        | r1_tarski(u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_pre_topc(X28,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X32] :
      ( ~ l1_pre_topc(X32)
      | ~ v2_tdlat_3(X32)
      | v2_pre_topc(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

cnf(c_0_30,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_33,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v2_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_37,plain,(
    ! [X10] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

fof(c_0_38,plain,(
    ! [X29,X30,X31] :
      ( ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | ~ m1_pre_topc(X31,X30)
      | m1_pre_topc(X31,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_26])])).

fof(c_0_42,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | m1_pre_topc(X25,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_43,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))
      | v2_pre_topc(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).

cnf(c_0_44,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_26])])).

cnf(c_0_48,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_41]),c_0_26])])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_26])])).

cnf(c_0_52,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34])])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34])])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_51]),c_0_34])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_34])])).

cnf(c_0_58,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_26])])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r1_tarski(u1_struct_0(esk2_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_58]),c_0_54]),c_0_34])])).

fof(c_0_61,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | m1_subset_1(u1_pre_topc(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    | ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_58])])).

fof(c_0_63,plain,(
    ! [X33] :
      ( ( ~ v2_tdlat_3(X33)
        | u1_pre_topc(X33) = k2_tarski(k1_xboole_0,u1_struct_0(X33))
        | ~ l1_pre_topc(X33) )
      & ( u1_pre_topc(X33) != k2_tarski(k1_xboole_0,u1_struct_0(X33))
        | v2_tdlat_3(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tdlat_3])])])).

fof(c_0_64,plain,(
    ! [X23,X24] :
      ( ( ~ v1_tops_2(X24,X23)
        | r1_tarski(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) )
      & ( ~ r1_tarski(X24,u1_pre_topc(X23))
        | v1_tops_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).

cnf(c_0_65,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_40]),c_0_53])])).

cnf(c_0_67,plain,
    ( u1_pre_topc(X1) = k2_tarski(k1_xboole_0,u1_struct_0(X1))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_68,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
      | ~ m1_pre_topc(X21,X19)
      | ~ v1_tops_2(X20,X19)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
      | X22 != X20
      | v1_tops_2(X22,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).

fof(c_0_69,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
      | m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_26])])).

cnf(c_0_72,plain,
    ( v2_tdlat_3(X1)
    | u1_pre_topc(X1) != k2_tarski(k1_xboole_0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k2_tarski(k1_xboole_0,u1_struct_0(esk2_0)) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_36]),c_0_26])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,plain,
    ( v1_tops_2(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,plain,
    ( v1_tops_2(X1,X2)
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0))
    | ~ v1_tops_2(u1_pre_topc(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_34])])).

cnf(c_0_79,negated_conjecture,
    ( u1_pre_topc(esk1_0) != u1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_34])]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk1_0))
    | ~ v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_66]),c_0_26])])).

cnf(c_0_81,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_75]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ r1_tarski(X1,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_66]),c_0_26])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_78]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))
    | ~ v1_tops_2(u1_pre_topc(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_65]),c_0_34])])).

cnf(c_0_85,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ v1_tops_2(u1_pre_topc(esk1_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_71])).

cnf(c_0_86,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_71]),c_0_31])])).

cnf(c_0_87,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_65]),c_0_28])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ v1_tops_2(u1_pre_topc(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk2_0)
    | ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_26])])).

cnf(c_0_90,plain,
    ( v1_tops_2(u1_pre_topc(X1),X2)
    | ~ v1_tops_2(u1_pre_topc(X1),X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_87]),c_0_28])).

cnf(c_0_91,plain,
    ( v1_tops_2(u1_pre_topc(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_65]),c_0_31])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk2_0),esk1_0)
    | ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,plain,
    ( v1_tops_2(u1_pre_topc(X1),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_58]),c_0_34])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_40]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t18_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v2_tdlat_3(X1))=>v2_tdlat_3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tex_2)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.13/0.38  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.13/0.38  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.13/0.38  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.13/0.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.38  fof(t58_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_pre_topc)).
% 0.13/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.13/0.38  fof(d2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)<=>u1_pre_topc(X1)=k2_tarski(k1_xboole_0,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tdlat_3)).
% 0.13/0.38  fof(t78_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>r1_tarski(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 0.13/0.38  fof(t35_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v1_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v1_tops_2(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 0.13/0.38  fof(t31_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v2_tdlat_3(X1))=>v2_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t18_tex_2])).
% 0.13/0.38  fof(c_0_17, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_18, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))|m1_pre_topc(X13,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, (l1_pre_topc(esk1_0)&(l1_pre_topc(esk2_0)&((g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&v2_tdlat_3(esk1_0))&~v2_tdlat_3(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X14, X15]:((~m1_pre_topc(X14,X15)|m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(~m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))|m1_pre_topc(X14,X15)|~l1_pre_topc(X15)|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X7, X8]:(~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|l1_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X26, X27, X28]:((~r1_tarski(u1_struct_0(X27),u1_struct_0(X28))|m1_pre_topc(X27,X28)|~m1_pre_topc(X28,X26)|~m1_pre_topc(X27,X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~m1_pre_topc(X27,X28)|r1_tarski(u1_struct_0(X27),u1_struct_0(X28))|~m1_pre_topc(X28,X26)|~m1_pre_topc(X27,X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.13/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_24, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_29, plain, ![X32]:(~l1_pre_topc(X32)|(~v2_tdlat_3(X32)|v2_pre_topc(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.13/0.38  cnf(c_0_30, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.13/0.38  cnf(c_0_33, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_35, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (v2_tdlat_3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_37, plain, ![X10]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))|(~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))|(~v2_pre_topc(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.13/0.38  fof(c_0_38, plain, ![X29, X30, X31]:(~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|(~m1_pre_topc(X31,X30)|m1_pre_topc(X31,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_pre_topc(X1,X1)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_26])])).
% 0.13/0.38  fof(c_0_42, plain, ![X25]:(~l1_pre_topc(X25)|m1_pre_topc(X25,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.38  fof(c_0_43, plain, ![X11]:(~l1_pre_topc(X11)|(~v2_pre_topc(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).
% 0.13/0.38  cnf(c_0_44, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_45, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_46, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_26])])).
% 0.13/0.38  cnf(c_0_48, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_49, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_41]), c_0_26])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_25]), c_0_26])])).
% 0.13/0.38  cnf(c_0_52, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~v2_pre_topc(X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_34])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_51]), c_0_34])])).
% 0.13/0.38  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_34])])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_26])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~r1_tarski(u1_struct_0(esk2_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_58]), c_0_54]), c_0_34])])).
% 0.13/0.38  fof(c_0_61, plain, ![X9]:(~l1_pre_topc(X9)|m1_subset_1(u1_pre_topc(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)|~m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_58])])).
% 0.13/0.38  fof(c_0_63, plain, ![X33]:((~v2_tdlat_3(X33)|u1_pre_topc(X33)=k2_tarski(k1_xboole_0,u1_struct_0(X33))|~l1_pre_topc(X33))&(u1_pre_topc(X33)!=k2_tarski(k1_xboole_0,u1_struct_0(X33))|v2_tdlat_3(X33)|~l1_pre_topc(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tdlat_3])])])).
% 0.13/0.38  fof(c_0_64, plain, ![X23, X24]:((~v1_tops_2(X24,X23)|r1_tarski(X24,u1_pre_topc(X23))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))&(~r1_tarski(X24,u1_pre_topc(X23))|v1_tops_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).
% 0.13/0.38  cnf(c_0_65, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_40]), c_0_53])])).
% 0.13/0.38  cnf(c_0_67, plain, (u1_pre_topc(X1)=k2_tarski(k1_xboole_0,u1_struct_0(X1))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  fof(c_0_68, plain, ![X19, X20, X21, X22]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|(~m1_pre_topc(X21,X19)|(~v1_tops_2(X20,X19)|(~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|(X22!=X20|v1_tops_2(X22,X21))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).
% 0.13/0.38  fof(c_0_69, plain, ![X16, X17, X18]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).
% 0.13/0.38  cnf(c_0_70, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v1_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_26])])).
% 0.13/0.38  cnf(c_0_72, plain, (v2_tdlat_3(X1)|u1_pre_topc(X1)!=k2_tarski(k1_xboole_0,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k2_tarski(k1_xboole_0,u1_struct_0(esk2_0))=u1_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_66]), c_0_36]), c_0_26])])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (~v2_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_75, plain, (v1_tops_2(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_pre_topc(X3,X1)|~v1_tops_2(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.13/0.38  cnf(c_0_76, plain, (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.13/0.38  cnf(c_0_77, plain, (v1_tops_2(X1,X2)|~r1_tarski(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0))|~v1_tops_2(u1_pre_topc(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_34])])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (u1_pre_topc(esk1_0)!=u1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_34])]), c_0_74])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk1_0))|~v1_tops_2(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_66]), c_0_26])])).
% 0.13/0.38  cnf(c_0_81, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_75]), c_0_76])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (v1_tops_2(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~r1_tarski(X1,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_66]), c_0_26])])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_78]), c_0_79])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))|~v1_tops_2(u1_pre_topc(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_65]), c_0_34])])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~v1_tops_2(u1_pre_topc(esk1_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_81, c_0_71])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_71]), c_0_31])])).
% 0.13/0.38  cnf(c_0_87, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_65]), c_0_28])).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~v1_tops_2(u1_pre_topc(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk2_0)|~m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_26])])).
% 0.13/0.38  cnf(c_0_90, plain, (v1_tops_2(u1_pre_topc(X1),X2)|~v1_tops_2(u1_pre_topc(X1),X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_87]), c_0_28])).
% 0.13/0.38  cnf(c_0_91, plain, (v1_tops_2(u1_pre_topc(X1),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_65]), c_0_31])])).
% 0.13/0.38  cnf(c_0_92, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk2_0),esk1_0)|~m1_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.13/0.38  cnf(c_0_93, plain, (v1_tops_2(u1_pre_topc(X1),X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.13/0.38  cnf(c_0_94, negated_conjecture, (~m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_58]), c_0_34])])).
% 0.13/0.38  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_40]), c_0_53])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 96
% 0.13/0.38  # Proof object clause steps            : 63
% 0.13/0.38  # Proof object formula steps           : 33
% 0.13/0.38  # Proof object conjectures             : 38
% 0.13/0.38  # Proof object clause conjectures      : 35
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 16
% 0.13/0.38  # Proof object generating inferences   : 35
% 0.13/0.38  # Proof object simplifying inferences  : 67
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 16
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 27
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 27
% 0.13/0.38  # Processed clauses                    : 221
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 71
% 0.13/0.38  # ...remaining for further processing  : 148
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 5
% 0.13/0.38  # Generated clauses                    : 369
% 0.13/0.38  # ...of the previous two non-trivial   : 283
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 366
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 114
% 0.13/0.38  #    Positive orientable unit clauses  : 16
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 95
% 0.13/0.38  # Current number of unprocessed clauses: 109
% 0.13/0.38  # ...number of literals in the above   : 505
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 2194
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1029
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 77
% 0.13/0.38  # Unit Clause-clause subsumption calls : 110
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 6
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 9996
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
