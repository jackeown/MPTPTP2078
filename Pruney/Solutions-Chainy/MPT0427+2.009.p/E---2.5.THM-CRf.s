%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:50 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 (1235 expanded)
%              Number of clauses        :   60 ( 527 expanded)
%              Number of leaves         :   15 ( 287 expanded)
%              Depth                    :   17
%              Number of atoms          :  168 (3481 expanded)
%              Number of equality atoms :   62 ( 765 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | k6_setfam_1(X21,X22) = k1_setfam_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ( X18 = k1_xboole_0
        | k8_setfam_1(X17,X18) = k6_setfam_1(X17,X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( X18 != k1_xboole_0
        | k8_setfam_1(X17,X18) = X17
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_19,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | X29 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X30),k1_setfam_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

fof(c_0_22,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))
      | m1_subset_1(k8_setfam_1(X19,X20),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk4_0) = k1_setfam_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( k8_setfam_1(esk2_0,esk4_0) = k1_setfam_1(esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk3_0) = k1_setfam_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k8_setfam_1(esk2_0,esk3_0) = esk2_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(k1_setfam_1(esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k8_setfam_1(esk2_0,esk3_0) = k1_setfam_1(esk3_0)
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_25]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))
    | ~ r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k8_setfam_1(esk2_0,k1_xboole_0) = esk2_0
    | r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k8_setfam_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_51,plain,(
    ! [X15,X16] :
      ( ~ v1_xboole_0(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_xboole_0(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_52,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_53,plain,(
    ! [X13] : m1_subset_1(esk1_1(X13),X13) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k8_setfam_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_27])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_61,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_62,negated_conjecture,
    ( k8_setfam_1(esk2_0,k1_xboole_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_54])).

fof(c_0_63,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k8_setfam_1(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_67,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_46]),c_0_62]),c_0_42])])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_46]),c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk4_0)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_74,plain,(
    ! [X9,X10] :
      ( ~ r2_hidden(X9,X10)
      | k2_xboole_0(k1_tarski(X9),X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k8_setfam_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_70]),c_0_62])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_72]),c_0_62])])).

cnf(c_0_80,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_73])).

fof(c_0_81,plain,(
    ! [X11,X12] : k2_xboole_0(k1_tarski(X11),X12) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_62]),c_0_79])])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_1(k1_xboole_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_70]),c_0_70])).

cnf(c_0_86,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1))))) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk1_1(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_86,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.20/0.41  # and selection function SelectComplexG.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t59_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 0.20/0.41  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.20/0.41  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.20/0.41  fof(t7_setfam_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.20/0.41  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.41  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.20/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.41  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.41  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.20/0.41  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.20/0.41  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t59_setfam_1])).
% 0.20/0.41  fof(c_0_16, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))|k6_setfam_1(X21,X22)=k1_setfam_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.20/0.41  fof(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.41  fof(c_0_18, plain, ![X17, X18]:((X18=k1_xboole_0|k8_setfam_1(X17,X18)=k6_setfam_1(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))&(X18!=k1_xboole_0|k8_setfam_1(X17,X18)=X17|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.20/0.41  cnf(c_0_19, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  fof(c_0_21, plain, ![X29, X30]:(~r1_tarski(X29,X30)|(X29=k1_xboole_0|r1_tarski(k1_setfam_1(X30),k1_setfam_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).
% 0.20/0.41  fof(c_0_22, plain, ![X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))|m1_subset_1(k8_setfam_1(X19,X20),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 0.20/0.41  cnf(c_0_23, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (k6_setfam_1(esk2_0,esk4_0)=k1_setfam_1(esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_26, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_28, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_29, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_30, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (~r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (k8_setfam_1(esk2_0,esk4_0)=k1_setfam_1(esk4_0)|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_24])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k6_setfam_1(esk2_0,esk3_0)=k1_setfam_1(esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (k8_setfam_1(esk2_0,esk3_0)=esk2_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(k1_setfam_1(esk4_0),k8_setfam_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (k8_setfam_1(esk2_0,esk3_0)=k1_setfam_1(esk3_0)|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_25]), c_0_33])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))|~r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_31, c_0_34])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (k8_setfam_1(esk2_0,k1_xboole_0)=esk2_0|r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (r1_tarski(k8_setfam_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|~r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_tarski(esk4_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_20])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_xboole_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.41  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_xboole_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  fof(c_0_51, plain, ![X15, X16]:(~v1_xboole_0(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_xboole_0(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.41  fof(c_0_52, plain, ![X25, X26]:(~m1_subset_1(X25,X26)|(v1_xboole_0(X26)|r2_hidden(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.41  fof(c_0_53, plain, ![X13]:m1_subset_1(esk1_1(X13),X13), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (m1_subset_1(k8_setfam_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.20/0.41  cnf(c_0_56, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_27])).
% 0.20/0.41  cnf(c_0_58, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.41  cnf(c_0_59, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.41  fof(c_0_60, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.41  fof(c_0_61, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (k8_setfam_1(esk2_0,k1_xboole_0)=esk2_0), inference(spm,[status(thm)],[c_0_28, c_0_54])).
% 0.20/0.41  fof(c_0_63, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (r1_tarski(k8_setfam_1(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_55])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.41  cnf(c_0_66, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.41  fof(c_0_67, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k5_xboole_0(X7,k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.41  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_69, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_46]), c_0_62]), c_0_42])])).
% 0.20/0.41  cnf(c_0_71, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_46]), c_0_62])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk4_0)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.41  fof(c_0_74, plain, ![X9, X10]:(~r2_hidden(X9,X10)|k2_xboole_0(k1_tarski(X9),X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.41  cnf(c_0_76, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (~r1_tarski(esk2_0,k8_setfam_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_70]), c_0_62])).
% 0.20/0.41  cnf(c_0_78, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_71, c_0_66])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (r1_tarski(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_72]), c_0_62])])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_73])).
% 0.20/0.41  fof(c_0_81, plain, ![X11, X12]:k2_xboole_0(k1_tarski(X11),X12)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.20/0.41  cnf(c_0_82, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.41  cnf(c_0_83, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_1(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_62]), c_0_79])])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_1(k1_xboole_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_70]), c_0_70])).
% 0.20/0.41  cnf(c_0_86, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.41  cnf(c_0_87, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1)))))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (r2_hidden(esk1_1(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.41  cnf(c_0_89, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1)))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_86, c_0_83])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 91
% 0.20/0.41  # Proof object clause steps            : 60
% 0.20/0.41  # Proof object formula steps           : 31
% 0.20/0.41  # Proof object conjectures             : 41
% 0.20/0.41  # Proof object clause conjectures      : 38
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 20
% 0.20/0.41  # Proof object initial formulas used   : 15
% 0.20/0.41  # Proof object generating inferences   : 33
% 0.20/0.41  # Proof object simplifying inferences  : 24
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 15
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 20
% 0.20/0.41  # Removed in clause preprocessing      : 3
% 0.20/0.41  # Initial clauses in saturation        : 17
% 0.20/0.41  # Processed clauses                    : 399
% 0.20/0.41  # ...of these trivial                  : 24
% 0.20/0.41  # ...subsumed                          : 94
% 0.20/0.41  # ...remaining for further processing  : 281
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 38
% 0.20/0.41  # Backward-rewritten                   : 142
% 0.20/0.41  # Generated clauses                    : 3145
% 0.20/0.41  # ...of the previous two non-trivial   : 3087
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 3145
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 84
% 0.20/0.41  #    Positive orientable unit clauses  : 30
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 52
% 0.20/0.41  # Current number of unprocessed clauses: 2597
% 0.20/0.41  # ...number of literals in the above   : 7719
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 200
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4578
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 3817
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 102
% 0.20/0.41  # Unit Clause-clause subsumption calls : 545
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 18
% 0.20/0.41  # BW rewrite match successes           : 18
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 33694
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.066 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.072 s
% 0.20/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
