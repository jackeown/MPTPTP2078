%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:13 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  132 (6972 expanded)
%              Number of clauses        :   93 (3359 expanded)
%              Number of leaves         :   19 (1794 expanded)
%              Depth                    :   27
%              Number of atoms          :  296 (11397 expanded)
%              Number of equality atoms :   94 (6379 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t75_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(fc11_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(l80_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

fof(c_0_19,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k2_xboole_0(X18,X19)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_20,plain,(
    ! [X15,X16,X17] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,k4_xboole_0(X14,X13))
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_25,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k3_subset_1(X24,k3_subset_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_27,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k3_subset_1(X20,X21) = k4_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_29]),c_0_29])).

fof(c_0_40,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t75_tops_1])).

cnf(c_0_42,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_48,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))) != k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_49,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_49]),c_0_50])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_55])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_56])).

fof(c_0_59,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_xboole_0(esk2_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X4,X2),X3) != k1_xboole_0
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_60])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | k4_xboole_0(X1,esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_60]),c_0_53])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_47])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_63])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_39])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_43])).

cnf(c_0_71,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_60])).

cnf(c_0_72,plain,
    ( m1_subset_1(k2_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_58])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_65]),c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_43]),c_0_39])])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_47])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) = k4_xboole_0(k4_xboole_0(X1,X3),X4)
    | ~ r1_tarski(X2,k2_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_68]),c_0_23])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(X1,u1_struct_0(esk1_0)) = k1_xboole_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_52])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,X2))
    | k4_xboole_0(k4_xboole_0(u1_struct_0(esk1_0),X1),X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_60])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,u1_struct_0(esk1_0)),X2) = k1_xboole_0
    | ~ r1_tarski(X3,k2_xboole_0(u1_struct_0(esk1_0),X2))
    | ~ r1_tarski(k4_xboole_0(X1,X3),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,k4_xboole_0(u1_struct_0(esk1_0),X1))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(X1,u1_struct_0(esk1_0)) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_43]),c_0_53])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_54])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) = k4_xboole_0(X1,X4)
    | ~ r1_tarski(k2_xboole_0(X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_68,c_0_23])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,esk2_0),u1_struct_0(esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_60])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X2,X4),X3)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_86])).

cnf(c_0_90,plain,
    ( k3_subset_1(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_91,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_75]),c_0_53])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk2_0),u1_struct_0(esk1_0)) = k4_xboole_0(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_70])])).

cnf(c_0_93,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(X3,X2)
    | ~ m1_subset_1(k2_xboole_0(X3,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_68])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_92])).

fof(c_0_96,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | m1_subset_1(k2_tops_1(X35,X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_97,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0)) = k2_xboole_0(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_38])])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_95])).

cnf(c_0_99,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

fof(c_0_100,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k7_subset_1(X26,X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_101,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | k2_tops_1(X39,X40) = k7_subset_1(u1_struct_0(X39),k2_pre_topc(X39,X40),k1_tops_1(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

fof(c_0_102,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_103,plain,(
    ! [X33,X34] :
      ( ( ~ v4_pre_topc(X34,X33)
        | k2_pre_topc(X33,X34) = X34
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) )
      & ( ~ v2_pre_topc(X33)
        | k2_pre_topc(X33,X34) != X34
        | v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_104,plain,(
    ! [X37,X38] :
      ( ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | v4_pre_topc(k2_tops_1(X37,X38),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_tops_1])])).

fof(c_0_105,plain,(
    ! [X43,X44] :
      ( ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | k2_tops_1(X43,X44) = k2_tops_1(X43,k3_subset_1(u1_struct_0(X43),X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_97]),c_0_52])])).

cnf(c_0_107,plain,
    ( m1_subset_1(k4_xboole_0(k2_xboole_0(X1,X2),X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_54])).

cnf(c_0_108,negated_conjecture,
    ( k2_xboole_0(esk2_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_98]),c_0_92]),c_0_43])])).

cnf(c_0_109,plain,
    ( k4_xboole_0(X1,u1_struct_0(X2)) = k1_xboole_0
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_tops_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_111,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_112,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_113,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_114,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,plain,
    ( v4_pre_topc(k2_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

fof(c_0_116,plain,(
    ! [X41,X42] :
      ( ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | k1_tops_1(X41,k2_tops_1(X41,k2_tops_1(X41,X42))) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l80_tops_1])])])).

cnf(c_0_117,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_118,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_106])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_120,negated_conjecture,
    ( k4_xboole_0(X1,u1_struct_0(esk1_0)) = k1_xboole_0
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_52]),c_0_110])])).

cnf(c_0_121,plain,
    ( k4_xboole_0(k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) = k2_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])).

cnf(c_0_122,plain,
    ( k2_pre_topc(X1,k2_tops_1(X1,X2)) = k2_tops_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_99])).

cnf(c_0_123,plain,
    ( k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2))) = k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_124,negated_conjecture,
    ( k2_tops_1(esk1_0,k4_xboole_0(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_110]),c_0_119])])).

cnf(c_0_125,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_120])).

cnf(c_0_127,plain,
    ( k4_xboole_0(k2_tops_1(X1,X2),k1_tops_1(X1,k2_tops_1(X1,X2))) = k2_tops_1(X1,k2_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_99])).

cnf(c_0_128,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125]),c_0_110]),c_0_119])])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_38])).

cnf(c_0_130,negated_conjecture,
    ( k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))) != k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_53]),c_0_125]),c_0_110]),c_0_129])]),c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.79/2.01  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.79/2.01  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.79/2.01  #
% 1.79/2.01  # Preprocessing time       : 0.031 s
% 1.79/2.01  # Presaturation interreduction done
% 1.79/2.01  
% 1.79/2.01  # Proof found!
% 1.79/2.01  # SZS status Theorem
% 1.79/2.01  # SZS output start CNFRefutation
% 1.79/2.01  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.79/2.01  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.79/2.01  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.79/2.01  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.79/2.01  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.79/2.01  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.79/2.01  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.79/2.01  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.79/2.01  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.79/2.01  fof(t75_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_1)).
% 1.79/2.01  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.79/2.01  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 1.79/2.01  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.79/2.01  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 1.79/2.01  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 1.79/2.01  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 1.79/2.01  fof(fc11_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_tops_1)).
% 1.79/2.01  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 1.79/2.01  fof(l80_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 1.79/2.01  fof(c_0_19, plain, ![X18, X19]:k4_xboole_0(X18,k2_xboole_0(X18,X19))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 1.79/2.01  fof(c_0_20, plain, ![X15, X16, X17]:k4_xboole_0(k4_xboole_0(X15,X16),X17)=k4_xboole_0(X15,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.79/2.01  fof(c_0_21, plain, ![X13, X14]:(~r1_tarski(X13,k4_xboole_0(X14,X13))|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 1.79/2.01  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.79/2.01  cnf(c_0_23, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.79/2.01  fof(c_0_24, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.79/2.01  fof(c_0_25, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.79/2.01  fof(c_0_26, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k3_subset_1(X24,k3_subset_1(X24,X25))=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 1.79/2.01  fof(c_0_27, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|k3_subset_1(X20,X21)=k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.79/2.01  cnf(c_0_28, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.79/2.01  cnf(c_0_29, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 1.79/2.01  cnf(c_0_30, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.79/2.01  fof(c_0_31, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.79/2.01  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.79/2.01  cnf(c_0_33, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.79/2.01  cnf(c_0_34, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.79/2.01  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.79/2.01  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 1.79/2.01  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.79/2.01  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 1.79/2.01  cnf(c_0_39, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_29]), c_0_29])).
% 1.79/2.01  fof(c_0_40, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.79/2.01  fof(c_0_41, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2))))), inference(assume_negation,[status(cth)],[t75_tops_1])).
% 1.79/2.01  cnf(c_0_42, plain, (k3_subset_1(X1,k4_xboole_0(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.79/2.01  cnf(c_0_43, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.79/2.01  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.79/2.01  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_39])).
% 1.79/2.01  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.79/2.01  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.79/2.01  fof(c_0_48, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))!=k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 1.79/2.01  cnf(c_0_49, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 1.79/2.01  cnf(c_0_50, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 1.79/2.01  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.79/2.01  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.79/2.01  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_49]), c_0_50])])).
% 1.79/2.01  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_43])).
% 1.79/2.01  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.79/2.01  cnf(c_0_56, plain, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.79/2.01  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_55])).
% 1.79/2.01  cnf(c_0_58, plain, (r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_56])).
% 1.79/2.01  fof(c_0_59, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.79/2.01  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_23])).
% 1.79/2.01  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_xboole_0(esk2_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.79/2.01  cnf(c_0_62, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.79/2.01  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.79/2.01  cnf(c_0_64, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X4,X2),X3)!=k1_xboole_0|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_46, c_0_60])).
% 1.79/2.01  cnf(c_0_65, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.79/2.01  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|k4_xboole_0(X1,esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_60]), c_0_53])).
% 1.79/2.01  cnf(c_0_67, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_47])).
% 1.79/2.01  cnf(c_0_68, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_23, c_0_63])).
% 1.79/2.01  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_39])])).
% 1.79/2.01  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_66, c_0_43])).
% 1.79/2.01  cnf(c_0_71, plain, (X1=k2_xboole_0(X2,X3)|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_60])).
% 1.79/2.01  cnf(c_0_72, plain, (m1_subset_1(k2_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_58])).
% 1.79/2.01  cnf(c_0_73, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_65]), c_0_39])).
% 1.79/2.01  cnf(c_0_74, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,X2))|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 1.79/2.01  cnf(c_0_75, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_43]), c_0_39])])).
% 1.79/2.01  cnf(c_0_76, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_73, c_0_47])).
% 1.79/2.01  cnf(c_0_77, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.79/2.01  cnf(c_0_78, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)=k4_xboole_0(k4_xboole_0(X1,X3),X4)|~r1_tarski(X2,k2_xboole_0(X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_68]), c_0_23])).
% 1.79/2.01  cnf(c_0_79, negated_conjecture, (k4_xboole_0(X1,u1_struct_0(esk1_0))=k1_xboole_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_76, c_0_52])).
% 1.79/2.01  cnf(c_0_80, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,X2))|k4_xboole_0(k4_xboole_0(u1_struct_0(esk1_0),X1),X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_60])).
% 1.79/2.01  cnf(c_0_81, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,u1_struct_0(esk1_0)),X2)=k1_xboole_0|~r1_tarski(X3,k2_xboole_0(u1_struct_0(esk1_0),X2))|~r1_tarski(k4_xboole_0(X1,X3),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_39])).
% 1.79/2.01  cnf(c_0_82, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,k4_xboole_0(u1_struct_0(esk1_0),X1)))), inference(spm,[status(thm)],[c_0_80, c_0_43])).
% 1.79/2.01  cnf(c_0_83, negated_conjecture, (k4_xboole_0(X1,u1_struct_0(esk1_0))=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_43]), c_0_53])).
% 1.79/2.01  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_54])).
% 1.79/2.01  cnf(c_0_85, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)=k4_xboole_0(X1,X4)|~r1_tarski(k2_xboole_0(X2,X3),X4)), inference(spm,[status(thm)],[c_0_68, c_0_23])).
% 1.79/2.01  cnf(c_0_86, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,esk2_0),u1_struct_0(esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.79/2.01  cnf(c_0_87, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_60])).
% 1.79/2.01  cnf(c_0_88, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X3)|~r1_tarski(k2_xboole_0(X2,X4),X3)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_68, c_0_85])).
% 1.79/2.01  cnf(c_0_89, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_86])).
% 1.79/2.01  cnf(c_0_90, plain, (k3_subset_1(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))=k2_xboole_0(X2,X3)|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 1.79/2.01  cnf(c_0_91, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_75]), c_0_53])).
% 1.79/2.01  cnf(c_0_92, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk2_0),u1_struct_0(esk1_0))=k4_xboole_0(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_70])])).
% 1.79/2.01  cnf(c_0_93, plain, (k3_subset_1(X1,k4_xboole_0(X1,X2))=k2_xboole_0(X3,X2)|~m1_subset_1(k2_xboole_0(X3,X2),k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_90, c_0_68])).
% 1.79/2.01  cnf(c_0_94, negated_conjecture, (m1_subset_1(k2_xboole_0(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_91, c_0_86])).
% 1.79/2.01  cnf(c_0_95, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_92])).
% 1.79/2.01  fof(c_0_96, plain, ![X35, X36]:(~l1_pre_topc(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|m1_subset_1(k2_tops_1(X35,X36),k1_zfmisc_1(u1_struct_0(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 1.79/2.01  cnf(c_0_97, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0))=k2_xboole_0(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_38])])).
% 1.79/2.01  cnf(c_0_98, negated_conjecture, (m1_subset_1(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_91, c_0_95])).
% 1.79/2.01  cnf(c_0_99, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 1.79/2.01  fof(c_0_100, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k7_subset_1(X26,X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 1.79/2.01  fof(c_0_101, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|k2_tops_1(X39,X40)=k7_subset_1(u1_struct_0(X39),k2_pre_topc(X39,X40),k1_tops_1(X39,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 1.79/2.01  fof(c_0_102, plain, ![X31, X32]:(~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 1.79/2.01  fof(c_0_103, plain, ![X33, X34]:((~v4_pre_topc(X34,X33)|k2_pre_topc(X33,X34)=X34|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))&(~v2_pre_topc(X33)|k2_pre_topc(X33,X34)!=X34|v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 1.79/2.01  fof(c_0_104, plain, ![X37, X38]:(~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|v4_pre_topc(k2_tops_1(X37,X38),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_tops_1])])).
% 1.79/2.01  fof(c_0_105, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|k2_tops_1(X43,X44)=k2_tops_1(X43,k3_subset_1(u1_struct_0(X43),X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 1.79/2.01  cnf(c_0_106, negated_conjecture, (k2_xboole_0(esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_97]), c_0_52])])).
% 1.79/2.01  cnf(c_0_107, plain, (m1_subset_1(k4_xboole_0(k2_xboole_0(X1,X2),X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_91, c_0_54])).
% 1.79/2.01  cnf(c_0_108, negated_conjecture, (k2_xboole_0(esk2_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_98]), c_0_92]), c_0_43])])).
% 1.79/2.01  cnf(c_0_109, plain, (k4_xboole_0(X1,u1_struct_0(X2))=k1_xboole_0|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_tops_1(X2,X3))), inference(spm,[status(thm)],[c_0_76, c_0_99])).
% 1.79/2.01  cnf(c_0_110, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.79/2.01  cnf(c_0_111, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 1.79/2.01  cnf(c_0_112, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 1.79/2.01  cnf(c_0_113, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.79/2.01  cnf(c_0_114, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.79/2.01  cnf(c_0_115, plain, (v4_pre_topc(k2_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 1.79/2.01  fof(c_0_116, plain, ![X41, X42]:(~v2_pre_topc(X41)|~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|k1_tops_1(X41,k2_tops_1(X41,k2_tops_1(X41,X42)))=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l80_tops_1])])])).
% 1.79/2.01  cnf(c_0_117, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 1.79/2.01  cnf(c_0_118, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k4_xboole_0(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_97, c_0_106])).
% 1.79/2.01  cnf(c_0_119, negated_conjecture, (m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 1.79/2.01  cnf(c_0_120, negated_conjecture, (k4_xboole_0(X1,u1_struct_0(esk1_0))=k1_xboole_0|~r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_52]), c_0_110])])).
% 1.79/2.01  cnf(c_0_121, plain, (k4_xboole_0(k2_pre_topc(X1,X2),k1_tops_1(X1,X2))=k2_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])).
% 1.79/2.01  cnf(c_0_122, plain, (k2_pre_topc(X1,k2_tops_1(X1,X2))=k2_tops_1(X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_99])).
% 1.79/2.01  cnf(c_0_123, plain, (k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X2)))=k1_xboole_0|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 1.79/2.01  cnf(c_0_124, negated_conjecture, (k2_tops_1(esk1_0,k4_xboole_0(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_110]), c_0_119])])).
% 1.79/2.01  cnf(c_0_125, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.79/2.01  cnf(c_0_126, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_91, c_0_120])).
% 1.79/2.01  cnf(c_0_127, plain, (k4_xboole_0(k2_tops_1(X1,X2),k1_tops_1(X1,k2_tops_1(X1,X2)))=k2_tops_1(X1,k2_tops_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_99])).
% 1.79/2.01  cnf(c_0_128, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_125]), c_0_110]), c_0_119])])).
% 1.79/2.01  cnf(c_0_129, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_126, c_0_38])).
% 1.79/2.01  cnf(c_0_130, negated_conjecture, (k2_tops_1(esk1_0,k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)))!=k2_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.79/2.01  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_53]), c_0_125]), c_0_110]), c_0_129])]), c_0_130]), ['proof']).
% 1.79/2.01  # SZS output end CNFRefutation
% 1.79/2.01  # Proof object total steps             : 132
% 1.79/2.01  # Proof object clause steps            : 93
% 1.79/2.01  # Proof object formula steps           : 39
% 1.79/2.01  # Proof object conjectures             : 36
% 1.79/2.01  # Proof object clause conjectures      : 33
% 1.79/2.01  # Proof object formula conjectures     : 3
% 1.79/2.01  # Proof object initial clauses used    : 25
% 1.79/2.01  # Proof object initial formulas used   : 19
% 1.79/2.01  # Proof object generating inferences   : 65
% 1.79/2.01  # Proof object simplifying inferences  : 47
% 1.79/2.01  # Training examples: 0 positive, 0 negative
% 1.79/2.01  # Parsed axioms                        : 20
% 1.79/2.01  # Removed by relevancy pruning/SinE    : 0
% 1.79/2.01  # Initial clauses                      : 28
% 1.79/2.01  # Removed in clause preprocessing      : 0
% 1.79/2.01  # Initial clauses in saturation        : 28
% 1.79/2.01  # Processed clauses                    : 20632
% 1.79/2.01  # ...of these trivial                  : 38
% 1.79/2.01  # ...subsumed                          : 18232
% 1.79/2.01  # ...remaining for further processing  : 2362
% 1.79/2.01  # Other redundant clauses eliminated   : 1611
% 1.79/2.01  # Clauses deleted for lack of memory   : 0
% 1.79/2.01  # Backward-subsumed                    : 227
% 1.79/2.01  # Backward-rewritten                   : 94
% 1.79/2.01  # Generated clauses                    : 157329
% 1.79/2.01  # ...of the previous two non-trivial   : 142843
% 1.79/2.01  # Contextual simplify-reflections      : 76
% 1.79/2.01  # Paramodulations                      : 155718
% 1.79/2.01  # Factorizations                       : 0
% 1.79/2.01  # Equation resolutions                 : 1611
% 1.79/2.01  # Propositional unsat checks           : 0
% 1.79/2.01  #    Propositional check models        : 0
% 1.79/2.01  #    Propositional check unsatisfiable : 0
% 1.79/2.01  #    Propositional clauses             : 0
% 1.79/2.01  #    Propositional clauses after purity: 0
% 1.79/2.01  #    Propositional unsat core size     : 0
% 1.79/2.01  #    Propositional preprocessing time  : 0.000
% 1.79/2.01  #    Propositional encoding time       : 0.000
% 1.79/2.01  #    Propositional solver time         : 0.000
% 1.79/2.01  #    Success case prop preproc time    : 0.000
% 1.79/2.01  #    Success case prop encoding time   : 0.000
% 1.79/2.01  #    Success case prop solver time     : 0.000
% 1.79/2.01  # Current number of processed clauses  : 2012
% 1.79/2.01  #    Positive orientable unit clauses  : 48
% 1.79/2.01  #    Positive unorientable unit clauses: 0
% 1.79/2.01  #    Negative unit clauses             : 16
% 1.79/2.01  #    Non-unit-clauses                  : 1948
% 1.79/2.01  # Current number of unprocessed clauses: 121716
% 1.79/2.01  # ...number of literals in the above   : 510565
% 1.79/2.01  # Current number of archived formulas  : 0
% 1.79/2.01  # Current number of archived clauses   : 348
% 1.79/2.01  # Clause-clause subsumption calls (NU) : 968081
% 1.79/2.01  # Rec. Clause-clause subsumption calls : 457407
% 1.79/2.01  # Non-unit clause-clause subsumptions  : 10518
% 1.79/2.01  # Unit Clause-clause subsumption calls : 12337
% 1.79/2.01  # Rewrite failures with RHS unbound    : 0
% 1.79/2.01  # BW rewrite match attempts            : 66
% 1.79/2.01  # BW rewrite match successes           : 28
% 1.79/2.01  # Condensation attempts                : 0
% 1.79/2.01  # Condensation successes               : 0
% 1.79/2.01  # Termbank termtop insertions          : 2546258
% 1.79/2.02  
% 1.79/2.02  # -------------------------------------------------
% 1.79/2.02  # User time                : 1.585 s
% 1.79/2.02  # System time              : 0.061 s
% 1.79/2.02  # Total time               : 1.645 s
% 1.79/2.02  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
