%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 210 expanded)
%              Number of clauses        :   49 (  90 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 488 expanded)
%              Number of equality atoms :   78 ( 156 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t15_xboole_1,axiom,(
    ! [X1,X2] :
      ( k2_xboole_0(X1,X2) = k1_xboole_0
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( ( ~ m1_subset_1(X33,k1_zfmisc_1(X34))
        | r1_tarski(X33,X34) )
      & ( ~ r1_tarski(X33,X34)
        | m1_subset_1(X33,k1_zfmisc_1(X34)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X25,X26] :
      ( ( X26 = k1_xboole_0
        | k8_setfam_1(X25,X26) = k6_setfam_1(X25,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))) )
      & ( X26 != k1_xboole_0
        | k8_setfam_1(X25,X26) = X25
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(k8_setfam_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27)))
      | m1_subset_1(k8_setfam_1(X27,X28),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ~ r1_tarski(X35,X36)
      | X35 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X36),k1_setfam_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,plain,(
    ! [X31,X32] : k1_setfam_1(k2_tarski(X31,X32)) = k3_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_33,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_36,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(X29)))
      | k6_setfam_1(X29,X30) = k1_setfam_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_39,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk3_0) = k8_setfam_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_38])).

fof(c_0_45,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k5_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_48,plain,(
    ! [X21,X22] :
      ( ( k4_xboole_0(k1_tarski(X21),k1_tarski(X22)) != k1_tarski(X21)
        | X21 != X22 )
      & ( X21 = X22
        | k4_xboole_0(k1_tarski(X21),k1_tarski(X22)) = k1_tarski(X21) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_49,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_50,plain,(
    ! [X23,X24] :
      ( ~ v1_xboole_0(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_xboole_0(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(esk3_0) = k8_setfam_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_26])])).

cnf(c_0_54,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk4_0) = k8_setfam_1(esk2_0,esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

fof(c_0_55,plain,(
    ! [X12,X13] :
      ( k2_xboole_0(X12,X13) != k1_xboole_0
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_58,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | k2_xboole_0(k1_tarski(X19),X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_61,plain,(
    ! [X14] : k5_xboole_0(X14,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k1_setfam_1(esk4_0) = k8_setfam_1(esk2_0,esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_54]),c_0_31])])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( X1 != X2
    | k5_xboole_0(k1_tarski(X1),k1_setfam_1(k1_enumset1(k1_tarski(X1),k1_tarski(X1),k1_tarski(X2)))) != k1_tarski(X1) ),
    inference(rw,[status(thm)],[c_0_59,c_0_57])).

cnf(c_0_70,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_60,c_0_47])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_72,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_21])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_tarski(X1))))) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_67])).

cnf(c_0_77,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_69]),c_0_70]),c_0_71])).

fof(c_0_78,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_38])).

cnf(c_0_84,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_83,c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t59_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.20/0.38  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 0.20/0.38  fof(t7_setfam_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.20/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.38  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.20/0.38  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.38  fof(t15_xboole_1, axiom, ![X1, X2]:(k2_xboole_0(X1,X2)=k1_xboole_0=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 0.20/0.38  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.20/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.38  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t59_setfam_1])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.38  fof(c_0_20, plain, ![X33, X34]:((~m1_subset_1(X33,k1_zfmisc_1(X34))|r1_tarski(X33,X34))&(~r1_tarski(X33,X34)|m1_subset_1(X33,k1_zfmisc_1(X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (~r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_23, plain, ![X25, X26]:((X26=k1_xboole_0|k8_setfam_1(X25,X26)=k6_setfam_1(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))))&(X26!=k1_xboole_0|k8_setfam_1(X25,X26)=X25|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (~m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(k8_setfam_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_25, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_27, plain, ![X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27)))|m1_subset_1(k8_setfam_1(X27,X28),k1_zfmisc_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 0.20/0.38  fof(c_0_28, plain, ![X35, X36]:(~r1_tarski(X35,X36)|(X35=k1_xboole_0|r1_tarski(k1_setfam_1(X36),k1_setfam_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (esk3_0!=k1_xboole_0|~m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.38  cnf(c_0_30, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_32, plain, ![X31, X32]:k1_setfam_1(k2_tarski(X31,X32))=k3_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.38  fof(c_0_33, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  cnf(c_0_34, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_36, plain, ![X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(X29)))|k6_setfam_1(X29,X30)=k1_setfam_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.20/0.38  cnf(c_0_37, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.20/0.38  fof(c_0_39, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.38  cnf(c_0_43, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (k6_setfam_1(esk2_0,esk3_0)=k8_setfam_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_38])).
% 0.20/0.38  fof(c_0_45, plain, ![X15, X16]:k2_xboole_0(X15,X16)=k5_xboole_0(X15,k4_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.38  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_47, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.38  fof(c_0_48, plain, ![X21, X22]:((k4_xboole_0(k1_tarski(X21),k1_tarski(X22))!=k1_tarski(X21)|X21!=X22)&(X21=X22|k4_xboole_0(k1_tarski(X21),k1_tarski(X22))=k1_tarski(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.20/0.38  fof(c_0_49, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.38  fof(c_0_50, plain, ![X23, X24]:(~v1_xboole_0(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_xboole_0(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.38  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))), inference(sr,[status(thm)],[c_0_42, c_0_38])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (k1_setfam_1(esk3_0)=k8_setfam_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_26])])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (k6_setfam_1(esk2_0,esk4_0)=k8_setfam_1(esk2_0,esk4_0)|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_31])).
% 0.20/0.38  fof(c_0_55, plain, ![X12, X13]:(k2_xboole_0(X12,X13)!=k1_xboole_0|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).
% 0.20/0.38  cnf(c_0_56, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_57, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  fof(c_0_58, plain, ![X19, X20]:(~r2_hidden(X19,X20)|k2_xboole_0(k1_tarski(X19),X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.20/0.38  cnf(c_0_59, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_60, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.38  fof(c_0_61, plain, ![X14]:k5_xboole_0(X14,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.38  cnf(c_0_62, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_35])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r1_tarski(k1_setfam_1(esk4_0),k8_setfam_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (k1_setfam_1(esk4_0)=k8_setfam_1(esk2_0,esk4_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_54]), c_0_31])])).
% 0.20/0.38  cnf(c_0_66, plain, (X1=k1_xboole_0|k2_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.38  cnf(c_0_67, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1))))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.38  cnf(c_0_68, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.38  cnf(c_0_69, plain, (X1!=X2|k5_xboole_0(k1_tarski(X1),k1_setfam_1(k1_enumset1(k1_tarski(X1),k1_tarski(X1),k1_tarski(X2))))!=k1_tarski(X1)), inference(rw,[status(thm)],[c_0_59, c_0_57])).
% 0.20/0.38  cnf(c_0_70, plain, (k1_setfam_1(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_60, c_0_47])).
% 0.20/0.38  cnf(c_0_71, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.38  fof(c_0_72, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_21])).
% 0.20/0.38  cnf(c_0_75, plain, (X1=k1_xboole_0|k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.38  cnf(c_0_76, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_tarski(X1)))))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_67])).
% 0.20/0.38  cnf(c_0_77, plain, (k1_tarski(X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_69]), c_0_70]), c_0_71])).
% 0.20/0.38  fof(c_0_78, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.38  cnf(c_0_79, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.38  cnf(c_0_80, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.38  cnf(c_0_81, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.20/0.38  cnf(c_0_82, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.38  cnf(c_0_83, negated_conjecture, (~v1_xboole_0(k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_38])).
% 0.20/0.38  cnf(c_0_84, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.38  cnf(c_0_85, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_83, c_0_84]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 86
% 0.20/0.38  # Proof object clause steps            : 49
% 0.20/0.38  # Proof object formula steps           : 37
% 0.20/0.38  # Proof object conjectures             : 23
% 0.20/0.38  # Proof object clause conjectures      : 20
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 23
% 0.20/0.38  # Proof object initial formulas used   : 18
% 0.20/0.38  # Proof object generating inferences   : 15
% 0.20/0.38  # Proof object simplifying inferences  : 25
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 18
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 25
% 0.20/0.38  # Removed in clause preprocessing      : 4
% 0.20/0.38  # Initial clauses in saturation        : 21
% 0.20/0.38  # Processed clauses                    : 114
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 24
% 0.20/0.38  # ...remaining for further processing  : 89
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 18
% 0.20/0.38  # Generated clauses                    : 163
% 0.20/0.38  # ...of the previous two non-trivial   : 166
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 161
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 67
% 0.20/0.38  #    Positive orientable unit clauses  : 14
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 9
% 0.20/0.38  #    Non-unit-clauses                  : 44
% 0.20/0.38  # Current number of unprocessed clauses: 52
% 0.20/0.38  # ...number of literals in the above   : 132
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 25
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 180
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 156
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.38  # Unit Clause-clause subsumption calls : 53
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 3
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3443
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.007 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
