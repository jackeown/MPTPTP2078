%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:20 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 840 expanded)
%              Number of clauses        :   62 ( 394 expanded)
%              Number of leaves         :   14 ( 220 expanded)
%              Depth                    :   19
%              Number of atoms          :  171 (1655 expanded)
%              Number of equality atoms :   43 ( 607 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_14,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X17,X18)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_15,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_16,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_17,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X21,X20)
        | r1_tarski(X21,X19)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r1_tarski(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r2_hidden(esk1_2(X23,X24),X24)
        | ~ r1_tarski(esk1_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) )
      & ( r2_hidden(esk1_2(X23,X24),X24)
        | r1_tarski(esk1_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,k3_subset_1(X31,X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_25,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | k3_subset_1(X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X27,X26)
        | r2_hidden(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ r2_hidden(X27,X26)
        | m1_subset_1(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ m1_subset_1(X27,X26)
        | v1_xboole_0(X27)
        | ~ v1_xboole_0(X26) )
      & ( ~ v1_xboole_0(X27)
        | m1_subset_1(X27,X26)
        | ~ v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X30] : ~ v1_xboole_0(k1_zfmisc_1(X30)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_21])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_23]),c_0_19])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X7,X8] : r1_tarski(k4_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k3_subset_1(X1,X2)) = X2
    | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k4_xboole_0(X14,X15),X16)
      | r1_tarski(X14,k2_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_43,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_18])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_33]),c_0_45])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_18]),c_0_47])])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(k2_xboole_0(X1,X3),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_57])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_59])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_60])).

cnf(c_0_64,plain,
    ( m1_subset_1(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk4_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_67,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))
    | ~ r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_45])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_63])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_31])).

cnf(c_0_71,plain,
    ( m1_subset_1(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_48])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_74,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_67,c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_68])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k4_xboole_0(k2_xboole_0(X3,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,esk2_0),k1_zfmisc_1(k4_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_33]),c_0_57])])).

fof(c_0_79,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | k4_subset_1(X33,X34,X35) = k2_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),esk2_0)
    | ~ r1_tarski(k4_xboole_0(X1,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(esk4_0,X1),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(k4_xboole_0(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_33])).

cnf(c_0_83,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_48])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_56]),c_0_57])])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_33]),c_0_45])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_85]),c_0_19])).

cnf(c_0_89,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_64])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_88]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.71/0.89  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.71/0.89  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.71/0.89  #
% 0.71/0.89  # Preprocessing time       : 0.027 s
% 0.71/0.89  # Presaturation interreduction done
% 0.71/0.89  
% 0.71/0.89  # Proof found!
% 0.71/0.89  # SZS status Theorem
% 0.71/0.89  # SZS output start CNFRefutation
% 0.71/0.89  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.71/0.89  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.71/0.89  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.71/0.89  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.71/0.89  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.71/0.89  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.71/0.89  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.71/0.89  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.71/0.89  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.71/0.89  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.71/0.89  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.71/0.89  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.71/0.89  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 0.71/0.89  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.71/0.89  fof(c_0_14, plain, ![X17, X18]:k4_xboole_0(X17,k2_xboole_0(X17,X18))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.71/0.89  fof(c_0_15, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.71/0.89  fof(c_0_16, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.71/0.89  fof(c_0_17, plain, ![X11, X12, X13]:k4_xboole_0(k4_xboole_0(X11,X12),X13)=k4_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.71/0.89  cnf(c_0_18, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.71/0.89  cnf(c_0_19, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.71/0.89  fof(c_0_20, plain, ![X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X21,X20)|r1_tarski(X21,X19)|X20!=k1_zfmisc_1(X19))&(~r1_tarski(X22,X19)|r2_hidden(X22,X20)|X20!=k1_zfmisc_1(X19)))&((~r2_hidden(esk1_2(X23,X24),X24)|~r1_tarski(esk1_2(X23,X24),X23)|X24=k1_zfmisc_1(X23))&(r2_hidden(esk1_2(X23,X24),X24)|r1_tarski(esk1_2(X23,X24),X23)|X24=k1_zfmisc_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.71/0.89  cnf(c_0_21, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.71/0.89  cnf(c_0_22, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.89  cnf(c_0_23, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.71/0.89  fof(c_0_24, plain, ![X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k3_subset_1(X31,k3_subset_1(X31,X32))=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.71/0.89  fof(c_0_25, plain, ![X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|k3_subset_1(X28,X29)=k4_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.71/0.89  fof(c_0_26, plain, ![X26, X27]:(((~m1_subset_1(X27,X26)|r2_hidden(X27,X26)|v1_xboole_0(X26))&(~r2_hidden(X27,X26)|m1_subset_1(X27,X26)|v1_xboole_0(X26)))&((~m1_subset_1(X27,X26)|v1_xboole_0(X27)|~v1_xboole_0(X26))&(~v1_xboole_0(X27)|m1_subset_1(X27,X26)|~v1_xboole_0(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.71/0.89  cnf(c_0_27, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.71/0.89  fof(c_0_28, plain, ![X30]:~v1_xboole_0(k1_zfmisc_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.71/0.89  cnf(c_0_29, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.71/0.89  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_21])).
% 0.71/0.89  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_23]), c_0_19])).
% 0.71/0.89  cnf(c_0_32, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.71/0.89  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.71/0.89  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.71/0.89  cnf(c_0_35, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_27])).
% 0.71/0.89  cnf(c_0_36, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.71/0.89  fof(c_0_37, plain, ![X7, X8]:r1_tarski(k4_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.71/0.89  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.71/0.89  cnf(c_0_39, plain, (k4_xboole_0(X1,k3_subset_1(X1,X2))=X2|~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.71/0.89  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.71/0.89  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.71/0.89  fof(c_0_42, plain, ![X14, X15, X16]:(~r1_tarski(k4_xboole_0(X14,X15),X16)|r1_tarski(X14,k2_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.71/0.89  fof(c_0_43, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.71/0.89  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=X1|~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.71/0.89  cnf(c_0_45, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.71/0.89  cnf(c_0_46, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.71/0.89  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_18])).
% 0.71/0.89  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.71/0.89  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_33]), c_0_45])])).
% 0.71/0.89  cnf(c_0_50, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_18]), c_0_47])])).
% 0.71/0.89  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.71/0.89  fof(c_0_52, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 0.71/0.89  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~m1_subset_1(k2_xboole_0(X1,X3),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.71/0.89  fof(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 0.71/0.89  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 0.71/0.89  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.71/0.89  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.71/0.89  cnf(c_0_58, negated_conjecture, (r1_tarski(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.71/0.89  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_55, c_0_57])).
% 0.71/0.89  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_46, c_0_41])).
% 0.71/0.89  cnf(c_0_61, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_58])).
% 0.71/0.89  cnf(c_0_62, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_59])).
% 0.71/0.89  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_60])).
% 0.71/0.89  cnf(c_0_64, plain, (m1_subset_1(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 0.71/0.89  cnf(c_0_65, plain, (k2_xboole_0(X1,X2)=X1|~m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_49])).
% 0.71/0.89  cnf(c_0_66, negated_conjecture, (m1_subset_1(k4_xboole_0(esk4_0,X1),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_45])).
% 0.71/0.89  cnf(c_0_67, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))|~r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(spm,[status(thm)],[c_0_46, c_0_22])).
% 0.71/0.89  cnf(c_0_68, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,X1),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_45])).
% 0.71/0.89  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_55, c_0_63])).
% 0.71/0.89  cnf(c_0_70, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_31])).
% 0.71/0.89  cnf(c_0_71, plain, (m1_subset_1(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_64, c_0_48])).
% 0.71/0.89  cnf(c_0_72, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.71/0.89  cnf(c_0_73, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.71/0.89  cnf(c_0_74, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_67, c_0_19])).
% 0.71/0.89  cnf(c_0_75, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0), inference(spm,[status(thm)],[c_0_65, c_0_68])).
% 0.71/0.89  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k4_xboole_0(k2_xboole_0(X3,X2),X3)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.71/0.89  cnf(c_0_77, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,esk2_0),k1_zfmisc_1(k4_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.71/0.89  cnf(c_0_78, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_33]), c_0_57])])).
% 0.71/0.89  fof(c_0_79, plain, ![X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|~m1_subset_1(X35,k1_zfmisc_1(X33))|k4_subset_1(X33,X34,X35)=k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.71/0.89  cnf(c_0_80, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),esk2_0)|~r1_tarski(k4_xboole_0(X1,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.71/0.89  cnf(c_0_81, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(esk4_0,X1),esk2_0),X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.71/0.89  cnf(c_0_82, negated_conjecture, (~m1_subset_1(k4_subset_1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0))|~r1_tarski(k4_xboole_0(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_78, c_0_33])).
% 0.71/0.89  cnf(c_0_83, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.71/0.89  cnf(c_0_84, plain, (r1_tarski(X1,X2)|~m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 0.71/0.89  cnf(c_0_85, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_48])).
% 0.71/0.89  cnf(c_0_86, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))|~r1_tarski(k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_56]), c_0_57])])).
% 0.71/0.89  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_33]), c_0_45])])).
% 0.71/0.89  cnf(c_0_88, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_85]), c_0_19])).
% 0.71/0.89  cnf(c_0_89, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_64])])).
% 0.71/0.89  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_88]), c_0_89]), ['proof']).
% 0.71/0.89  # SZS output end CNFRefutation
% 0.71/0.89  # Proof object total steps             : 91
% 0.71/0.89  # Proof object clause steps            : 62
% 0.71/0.89  # Proof object formula steps           : 29
% 0.71/0.89  # Proof object conjectures             : 24
% 0.71/0.89  # Proof object clause conjectures      : 21
% 0.71/0.89  # Proof object formula conjectures     : 3
% 0.71/0.89  # Proof object initial clauses used    : 16
% 0.71/0.89  # Proof object initial formulas used   : 14
% 0.71/0.89  # Proof object generating inferences   : 45
% 0.71/0.89  # Proof object simplifying inferences  : 22
% 0.71/0.89  # Training examples: 0 positive, 0 negative
% 0.71/0.89  # Parsed axioms                        : 14
% 0.71/0.89  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.89  # Initial clauses                      : 22
% 0.71/0.89  # Removed in clause preprocessing      : 0
% 0.71/0.89  # Initial clauses in saturation        : 22
% 0.71/0.89  # Processed clauses                    : 5514
% 0.71/0.89  # ...of these trivial                  : 222
% 0.71/0.89  # ...subsumed                          : 4478
% 0.71/0.89  # ...remaining for further processing  : 814
% 0.71/0.89  # Other redundant clauses eliminated   : 2
% 0.71/0.89  # Clauses deleted for lack of memory   : 0
% 0.71/0.89  # Backward-subsumed                    : 17
% 0.71/0.89  # Backward-rewritten                   : 9
% 0.71/0.89  # Generated clauses                    : 52745
% 0.71/0.89  # ...of the previous two non-trivial   : 41308
% 0.71/0.89  # Contextual simplify-reflections      : 9
% 0.71/0.89  # Paramodulations                      : 52735
% 0.71/0.89  # Factorizations                       : 8
% 0.71/0.89  # Equation resolutions                 : 2
% 0.71/0.89  # Propositional unsat checks           : 0
% 0.71/0.89  #    Propositional check models        : 0
% 0.71/0.89  #    Propositional check unsatisfiable : 0
% 0.71/0.89  #    Propositional clauses             : 0
% 0.71/0.89  #    Propositional clauses after purity: 0
% 0.71/0.89  #    Propositional unsat core size     : 0
% 0.71/0.89  #    Propositional preprocessing time  : 0.000
% 0.71/0.89  #    Propositional encoding time       : 0.000
% 0.71/0.89  #    Propositional solver time         : 0.000
% 0.71/0.89  #    Success case prop preproc time    : 0.000
% 0.71/0.89  #    Success case prop encoding time   : 0.000
% 0.71/0.89  #    Success case prop solver time     : 0.000
% 0.71/0.89  # Current number of processed clauses  : 764
% 0.71/0.89  #    Positive orientable unit clauses  : 189
% 0.71/0.89  #    Positive unorientable unit clauses: 3
% 0.71/0.89  #    Negative unit clauses             : 20
% 0.71/0.89  #    Non-unit-clauses                  : 552
% 0.71/0.89  # Current number of unprocessed clauses: 35781
% 0.71/0.89  # ...number of literals in the above   : 98215
% 0.71/0.89  # Current number of archived formulas  : 0
% 0.71/0.89  # Current number of archived clauses   : 48
% 0.71/0.89  # Clause-clause subsumption calls (NU) : 140848
% 0.71/0.89  # Rec. Clause-clause subsumption calls : 119797
% 0.71/0.89  # Non-unit clause-clause subsumptions  : 3177
% 0.71/0.89  # Unit Clause-clause subsumption calls : 1370
% 0.71/0.89  # Rewrite failures with RHS unbound    : 0
% 0.71/0.89  # BW rewrite match attempts            : 965
% 0.71/0.89  # BW rewrite match successes           : 76
% 0.71/0.89  # Condensation attempts                : 0
% 0.71/0.89  # Condensation successes               : 0
% 0.71/0.89  # Termbank termtop insertions          : 684542
% 0.71/0.89  
% 0.71/0.89  # -------------------------------------------------
% 0.71/0.89  # User time                : 0.512 s
% 0.71/0.89  # System time              : 0.022 s
% 0.71/0.89  # Total time               : 0.534 s
% 0.71/0.89  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
