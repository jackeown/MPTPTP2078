%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:06 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 959 expanded)
%              Number of clauses        :   89 ( 458 expanded)
%              Number of leaves         :   24 ( 246 expanded)
%              Depth                    :   21
%              Number of atoms          :  266 (1403 expanded)
%              Number of equality atoms :   67 ( 723 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t69_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t31_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(c_0_24,plain,(
    ! [X15] : k2_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_25,plain,(
    ! [X33,X34] : k3_tarski(k2_tarski(X33,X34)) = k2_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_31,plain,(
    ! [X51,X52] : k1_setfam_1(k2_tarski(X51,X52)) = k3_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_32,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(k2_xboole_0(X8,X9),X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tops_1])).

fof(c_0_34,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X53,k1_zfmisc_1(X54))
        | r1_tarski(X53,X54) )
      & ( ~ r1_tarski(X53,X54)
        | m1_subset_1(X53,k1_zfmisc_1(X54)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_pre_topc(esk2_0,esk1_0)
    & ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

fof(c_0_42,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_45,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_47,plain,(
    ! [X31,X32] : k2_tarski(X31,X32) = k2_tarski(X32,X31) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_58,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_59,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_61,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_62,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_65,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_66,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_55])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_70,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(k4_xboole_0(X24,X25),X26)
      | r1_tarski(X24,k2_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_72,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_64,c_0_52])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_74,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k2_xboole_0(X22,X23))
      | r1_tarski(k4_xboole_0(X21,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_75,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_54]),c_0_68])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_28])).

cnf(c_0_78,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_55])).

fof(c_0_79,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_88,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,k4_xboole_0(X19,X18))
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_28]),c_0_52])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_28]),c_0_52])).

cnf(c_0_92,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_38]),c_0_52]),c_0_52])).

cnf(c_0_94,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_55])).

cnf(c_0_97,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_67]),c_0_77])]),c_0_92])])).

cnf(c_0_98,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_93])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_94,c_0_52])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_77])).

cnf(c_0_102,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_97])).

fof(c_0_103,plain,(
    ! [X57,X58,X59] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X57)))
      | ~ v4_pre_topc(X58,X57)
      | ~ r1_tarski(X59,X58)
      | r1_tarski(k2_pre_topc(X57,X59),X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

cnf(c_0_104,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_98])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_91])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_107,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_102]),c_0_92])])).

cnf(c_0_108,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_85]),c_0_72])])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_107])])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,X2)
    | ~ v4_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X1,k2_pre_topc(X3,X4))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_114,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_55])).

cnf(c_0_115,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,X1)) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_110]),c_0_111]),c_0_107])])).

fof(c_0_116,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k4_subset_1(X42,X43,X44) = k2_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ v4_pre_topc(X2,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_50]),c_0_113])])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_120,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

fof(c_0_121,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | k2_pre_topc(X62,X63) = k4_subset_1(u1_struct_0(X62),X63,k2_tops_1(X62,X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_122,plain,(
    ! [X55,X56] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | m1_subset_1(k2_tops_1(X55,X56),k1_zfmisc_1(u1_struct_0(X55))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119]),c_0_82]),c_0_82])])).

cnf(c_0_124,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_120,c_0_28])).

cnf(c_0_125,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_126,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_127,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_82])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,k4_subset_1(X2,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_124])).

cnf(c_0_130,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_55])).

cnf(c_0_131,plain,
    ( k3_tarski(k2_tarski(X1,k2_tops_1(X2,X1))) = k2_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126])).

cnf(c_0_132,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_133,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X1))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_125]),c_0_126])).

cnf(c_0_134,plain,
    ( r1_tarski(k2_tops_1(X1,X2),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_113]),c_0_50])])).

cnf(c_0_136,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_137,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_113]),c_0_50])]),c_0_136]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.46/1.67  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.46/1.67  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.46/1.67  #
% 1.46/1.67  # Preprocessing time       : 0.031 s
% 1.46/1.67  # Presaturation interreduction done
% 1.46/1.67  
% 1.46/1.67  # Proof found!
% 1.46/1.67  # SZS status Theorem
% 1.46/1.67  # SZS output start CNFRefutation
% 1.46/1.67  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.46/1.67  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.46/1.67  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.46/1.67  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.46/1.67  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.46/1.67  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.46/1.67  fof(t69_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 1.46/1.67  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.46/1.67  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.46/1.67  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.46/1.67  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.46/1.67  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.46/1.67  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.46/1.67  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.46/1.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.46/1.67  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.46/1.67  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.46/1.67  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.46/1.67  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.46/1.67  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.46/1.67  fof(t31_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 1.46/1.67  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.46/1.67  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 1.46/1.67  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 1.46/1.67  fof(c_0_24, plain, ![X15]:k2_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.46/1.67  fof(c_0_25, plain, ![X33, X34]:k3_tarski(k2_tarski(X33,X34))=k2_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.46/1.67  fof(c_0_26, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.46/1.67  cnf(c_0_27, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.46/1.67  cnf(c_0_28, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.46/1.67  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.46/1.67  fof(c_0_30, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.46/1.67  fof(c_0_31, plain, ![X51, X52]:k1_setfam_1(k2_tarski(X51,X52))=k3_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.46/1.67  fof(c_0_32, plain, ![X8, X9, X10]:(~r1_tarski(k2_xboole_0(X8,X9),X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 1.46/1.67  fof(c_0_33, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t69_tops_1])).
% 1.46/1.67  fof(c_0_34, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.46/1.67  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 1.46/1.67  cnf(c_0_36, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 1.46/1.67  cnf(c_0_37, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.46/1.67  cnf(c_0_38, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.46/1.67  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.46/1.67  fof(c_0_40, plain, ![X53, X54]:((~m1_subset_1(X53,k1_zfmisc_1(X54))|r1_tarski(X53,X54))&(~r1_tarski(X53,X54)|m1_subset_1(X53,k1_zfmisc_1(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.46/1.67  fof(c_0_41, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_pre_topc(esk2_0,esk1_0)&~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 1.46/1.67  fof(c_0_42, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.46/1.67  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.46/1.67  fof(c_0_44, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.46/1.67  cnf(c_0_45, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.46/1.67  cnf(c_0_46, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 1.46/1.67  fof(c_0_47, plain, ![X31, X32]:k2_tarski(X31,X32)=k2_tarski(X32,X31), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.46/1.67  cnf(c_0_48, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_39, c_0_28])).
% 1.46/1.67  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.46/1.67  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.46/1.67  cnf(c_0_51, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.46/1.67  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_43, c_0_38])).
% 1.46/1.67  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.46/1.67  cnf(c_0_54, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.46/1.67  cnf(c_0_55, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.46/1.67  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_48, c_0_36])).
% 1.46/1.67  cnf(c_0_57, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.46/1.67  fof(c_0_58, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.46/1.67  cnf(c_0_59, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 1.46/1.67  cnf(c_0_60, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_53, c_0_52])).
% 1.46/1.67  cnf(c_0_61, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.46/1.67  fof(c_0_62, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.46/1.67  cnf(c_0_63, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.46/1.67  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.46/1.67  fof(c_0_65, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.46/1.67  fof(c_0_66, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.46/1.67  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_55])).
% 1.46/1.67  cnf(c_0_68, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 1.46/1.67  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.46/1.67  fof(c_0_70, plain, ![X24, X25, X26]:(~r1_tarski(k4_xboole_0(X24,X25),X26)|r1_tarski(X24,k2_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.46/1.67  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_63])).
% 1.46/1.67  cnf(c_0_72, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_64, c_0_52])).
% 1.46/1.67  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.46/1.67  fof(c_0_74, plain, ![X21, X22, X23]:(~r1_tarski(X21,k2_xboole_0(X22,X23))|r1_tarski(k4_xboole_0(X21,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.46/1.67  cnf(c_0_75, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.46/1.67  cnf(c_0_76, plain, (k3_subset_1(X1,k1_xboole_0)=X1|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_54]), c_0_68])).
% 1.46/1.67  cnf(c_0_77, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_69, c_0_28])).
% 1.46/1.67  cnf(c_0_78, plain, (k3_tarski(k2_tarski(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_35, c_0_55])).
% 1.46/1.67  fof(c_0_79, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.46/1.67  cnf(c_0_80, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.46/1.67  cnf(c_0_81, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2))))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 1.46/1.67  cnf(c_0_82, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 1.46/1.67  cnf(c_0_83, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 1.46/1.67  cnf(c_0_84, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 1.46/1.67  cnf(c_0_85, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.46/1.67  cnf(c_0_86, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.46/1.67  cnf(c_0_87, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 1.46/1.67  fof(c_0_88, plain, ![X18, X19]:(~r1_tarski(X18,k4_xboole_0(X19,X18))|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 1.46/1.67  cnf(c_0_89, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_28]), c_0_52])).
% 1.46/1.67  cnf(c_0_90, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.46/1.67  cnf(c_0_91, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_28]), c_0_52])).
% 1.46/1.67  cnf(c_0_92, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 1.46/1.67  cnf(c_0_93, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_38]), c_0_52]), c_0_52])).
% 1.46/1.67  cnf(c_0_94, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 1.46/1.67  cnf(c_0_95, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.46/1.67  cnf(c_0_96, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_55])).
% 1.46/1.67  cnf(c_0_97, plain, (r1_tarski(k3_subset_1(X1,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_67]), c_0_77])]), c_0_92])])).
% 1.46/1.67  cnf(c_0_98, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_93])).
% 1.46/1.67  cnf(c_0_99, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_94, c_0_52])).
% 1.46/1.67  cnf(c_0_100, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 1.46/1.67  cnf(c_0_101, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_77])).
% 1.46/1.67  cnf(c_0_102, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_97])).
% 1.46/1.67  fof(c_0_103, plain, ![X57, X58, X59]:(~l1_pre_topc(X57)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|(~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X57)))|(~v4_pre_topc(X58,X57)|~r1_tarski(X59,X58)|r1_tarski(k2_pre_topc(X57,X59),X58))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).
% 1.46/1.67  cnf(c_0_104, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_98])).
% 1.46/1.67  cnf(c_0_105, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,k3_tarski(k2_tarski(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))))))), inference(spm,[status(thm)],[c_0_99, c_0_91])).
% 1.46/1.67  cnf(c_0_106, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 1.46/1.67  cnf(c_0_107, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_102]), c_0_92])])).
% 1.46/1.67  cnf(c_0_108, plain, (r1_tarski(k2_pre_topc(X1,X3),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.46/1.67  cnf(c_0_109, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_85]), c_0_72])])).
% 1.46/1.67  cnf(c_0_110, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k1_xboole_0|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 1.46/1.67  cnf(c_0_111, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_107])])).
% 1.46/1.67  cnf(c_0_112, plain, (r1_tarski(X1,X2)|~v4_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X1,k2_pre_topc(X3,X4))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_56, c_0_108])).
% 1.46/1.67  cnf(c_0_113, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.46/1.67  cnf(c_0_114, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_109, c_0_55])).
% 1.46/1.67  cnf(c_0_115, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,X1))=esk2_0|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_110]), c_0_111]), c_0_107])])).
% 1.46/1.67  fof(c_0_116, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|~m1_subset_1(X44,k1_zfmisc_1(X42))|k4_subset_1(X42,X43,X44)=k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 1.46/1.67  cnf(c_0_117, negated_conjecture, (r1_tarski(X1,X2)|~v4_pre_topc(X2,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(esk2_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_50]), c_0_113])])).
% 1.46/1.67  cnf(c_0_118, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 1.46/1.67  cnf(c_0_119, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.46/1.67  cnf(c_0_120, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 1.46/1.67  fof(c_0_121, plain, ![X62, X63]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|k2_pre_topc(X62,X63)=k4_subset_1(u1_struct_0(X62),X63,k2_tops_1(X62,X63)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 1.46/1.67  fof(c_0_122, plain, ![X55, X56]:(~l1_pre_topc(X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|m1_subset_1(k2_tops_1(X55,X56),k1_zfmisc_1(u1_struct_0(X55)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 1.46/1.67  cnf(c_0_123, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119]), c_0_82]), c_0_82])])).
% 1.46/1.67  cnf(c_0_124, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_120, c_0_28])).
% 1.46/1.67  cnf(c_0_125, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_121])).
% 1.46/1.67  cnf(c_0_126, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_122])).
% 1.46/1.67  cnf(c_0_127, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.46/1.67  cnf(c_0_128, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_123, c_0_82])).
% 1.46/1.67  cnf(c_0_129, plain, (r1_tarski(X1,k4_subset_1(X2,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_77, c_0_124])).
% 1.46/1.67  cnf(c_0_130, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_77, c_0_55])).
% 1.46/1.67  cnf(c_0_131, plain, (k3_tarski(k2_tarski(X1,k2_tops_1(X2,X1)))=k2_pre_topc(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126])).
% 1.46/1.67  cnf(c_0_132, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 1.46/1.67  cnf(c_0_133, plain, (r1_tarski(X1,k2_pre_topc(X2,X1))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_125]), c_0_126])).
% 1.46/1.67  cnf(c_0_134, plain, (r1_tarski(k2_tops_1(X1,X2),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 1.46/1.67  cnf(c_0_135, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_113]), c_0_50])])).
% 1.46/1.67  cnf(c_0_136, negated_conjecture, (~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.46/1.67  cnf(c_0_137, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_113]), c_0_50])]), c_0_136]), ['proof']).
% 1.46/1.67  # SZS output end CNFRefutation
% 1.46/1.67  # Proof object total steps             : 138
% 1.46/1.67  # Proof object clause steps            : 89
% 1.46/1.67  # Proof object formula steps           : 49
% 1.46/1.67  # Proof object conjectures             : 24
% 1.46/1.67  # Proof object clause conjectures      : 21
% 1.46/1.67  # Proof object formula conjectures     : 3
% 1.46/1.67  # Proof object initial clauses used    : 29
% 1.46/1.67  # Proof object initial formulas used   : 24
% 1.46/1.67  # Proof object generating inferences   : 43
% 1.46/1.67  # Proof object simplifying inferences  : 51
% 1.46/1.67  # Training examples: 0 positive, 0 negative
% 1.46/1.67  # Parsed axioms                        : 28
% 1.46/1.67  # Removed by relevancy pruning/SinE    : 0
% 1.46/1.67  # Initial clauses                      : 34
% 1.46/1.67  # Removed in clause preprocessing      : 3
% 1.46/1.67  # Initial clauses in saturation        : 31
% 1.46/1.67  # Processed clauses                    : 13107
% 1.46/1.67  # ...of these trivial                  : 75
% 1.46/1.67  # ...subsumed                          : 10970
% 1.46/1.67  # ...remaining for further processing  : 2062
% 1.46/1.67  # Other redundant clauses eliminated   : 2
% 1.46/1.67  # Clauses deleted for lack of memory   : 0
% 1.46/1.67  # Backward-subsumed                    : 204
% 1.46/1.67  # Backward-rewritten                   : 70
% 1.46/1.67  # Generated clauses                    : 115792
% 1.46/1.67  # ...of the previous two non-trivial   : 105506
% 1.46/1.67  # Contextual simplify-reflections      : 46
% 1.46/1.67  # Paramodulations                      : 115790
% 1.46/1.67  # Factorizations                       : 0
% 1.46/1.67  # Equation resolutions                 : 2
% 1.46/1.67  # Propositional unsat checks           : 0
% 1.46/1.67  #    Propositional check models        : 0
% 1.46/1.67  #    Propositional check unsatisfiable : 0
% 1.46/1.67  #    Propositional clauses             : 0
% 1.46/1.67  #    Propositional clauses after purity: 0
% 1.46/1.67  #    Propositional unsat core size     : 0
% 1.46/1.67  #    Propositional preprocessing time  : 0.000
% 1.46/1.67  #    Propositional encoding time       : 0.000
% 1.46/1.67  #    Propositional solver time         : 0.000
% 1.46/1.67  #    Success case prop preproc time    : 0.000
% 1.46/1.67  #    Success case prop encoding time   : 0.000
% 1.46/1.67  #    Success case prop solver time     : 0.000
% 1.46/1.67  # Current number of processed clauses  : 1756
% 1.46/1.67  #    Positive orientable unit clauses  : 140
% 1.46/1.67  #    Positive unorientable unit clauses: 1
% 1.46/1.67  #    Negative unit clauses             : 55
% 1.46/1.67  #    Non-unit-clauses                  : 1560
% 1.46/1.67  # Current number of unprocessed clauses: 91987
% 1.46/1.67  # ...number of literals in the above   : 325034
% 1.46/1.67  # Current number of archived formulas  : 0
% 1.46/1.67  # Current number of archived clauses   : 307
% 1.46/1.67  # Clause-clause subsumption calls (NU) : 647591
% 1.46/1.67  # Rec. Clause-clause subsumption calls : 257087
% 1.46/1.67  # Non-unit clause-clause subsumptions  : 6923
% 1.46/1.67  # Unit Clause-clause subsumption calls : 14518
% 1.46/1.67  # Rewrite failures with RHS unbound    : 0
% 1.46/1.67  # BW rewrite match attempts            : 2061
% 1.46/1.67  # BW rewrite match successes           : 54
% 1.46/1.67  # Condensation attempts                : 0
% 1.46/1.67  # Condensation successes               : 0
% 1.46/1.67  # Termbank termtop insertions          : 2570841
% 1.46/1.68  
% 1.46/1.68  # -------------------------------------------------
% 1.46/1.68  # User time                : 1.294 s
% 1.46/1.68  # System time              : 0.046 s
% 1.46/1.68  # Total time               : 1.340 s
% 1.46/1.68  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
