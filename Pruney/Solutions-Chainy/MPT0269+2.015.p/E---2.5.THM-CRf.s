%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:29 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 719 expanded)
%              Number of clauses        :   54 ( 316 expanded)
%              Number of leaves         :   12 ( 196 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 (1085 expanded)
%              Number of equality atoms :   65 ( 740 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t66_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
        & X1 != k1_xboole_0
        & X1 != k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_12,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
          & X1 != k1_xboole_0
          & X1 != k1_tarski(X2) ) ),
    inference(assume_negation,[status(cth)],[t66_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,X12) != k1_xboole_0
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | k4_xboole_0(X11,X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_17,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,negated_conjecture,
    ( k4_xboole_0(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0
    & esk1_0 != k1_xboole_0
    & esk1_0 != k1_tarski(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_21,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X24,X25,X26] :
      ( ( r2_hidden(X24,X26)
        | ~ r1_tarski(k2_tarski(X24,X25),X26) )
      & ( r2_hidden(X25,X26)
        | ~ r1_tarski(k2_tarski(X24,X25),X26) )
      & ( ~ r2_hidden(X24,X26)
        | ~ r2_hidden(X25,X26)
        | r1_tarski(k2_tarski(X24,X25),X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_19]),c_0_33])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X6,k5_xboole_0(X7,X8)) )
      & ( r2_hidden(X6,X7)
        | r2_hidden(X6,X8)
        | ~ r2_hidden(X6,k5_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X6,X7)
        | r2_hidden(X6,X8)
        | r2_hidden(X6,k5_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X6,X8)
        | r2_hidden(X6,X7)
        | r2_hidden(X6,k5_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_32]),c_0_33])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk1_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_41]),c_0_35]),c_0_42])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_43]),c_0_34])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)) = k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_48])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_49])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_32]),c_0_33])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k5_xboole_0(k2_enumset1(X2,X2,X2,X1),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_40])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_61,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X2),X4))
    | r2_hidden(X2,X4)
    | ~ r2_hidden(X1,k5_xboole_0(k2_enumset1(X3,X3,X3,X2),X4)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0) = k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)
    | ~ r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X1),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_48]),c_0_35]),c_0_48])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0) = k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)
    | r2_hidden(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk1_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_48]),c_0_65])])).

cnf(c_0_71,negated_conjecture,
    ( esk1_0 != k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_55]),c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_70]),c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k5_xboole_0(X1,esk1_0))
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_67]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k5_xboole_0(k2_enumset1(X1,X1,X1,esk2_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_52])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_76,c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.37/0.54  # and selection function SelectCQIArNpEqFirst.
% 0.37/0.54  #
% 0.37/0.54  # Preprocessing time       : 0.027 s
% 0.37/0.54  # Presaturation interreduction done
% 0.37/0.54  
% 0.37/0.54  # Proof found!
% 0.37/0.54  # SZS status Theorem
% 0.37/0.54  # SZS output start CNFRefutation
% 0.37/0.54  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.37/0.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.37/0.54  fof(t66_zfmisc_1, conjecture, ![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 0.37/0.54  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.37/0.54  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.37/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.54  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.37/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.54  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.37/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.54  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.37/0.54  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.37/0.54  fof(c_0_12, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.37/0.54  fof(c_0_13, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.37/0.54  fof(c_0_14, negated_conjecture, ~(![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t66_zfmisc_1])).
% 0.37/0.54  fof(c_0_15, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.37/0.54  fof(c_0_16, plain, ![X11, X12]:((k4_xboole_0(X11,X12)!=k1_xboole_0|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|k4_xboole_0(X11,X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.37/0.54  fof(c_0_17, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.54  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.37/0.54  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.54  fof(c_0_20, negated_conjecture, ((k4_xboole_0(esk1_0,k1_tarski(esk2_0))=k1_xboole_0&esk1_0!=k1_xboole_0)&esk1_0!=k1_tarski(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.37/0.54  fof(c_0_21, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.37/0.54  fof(c_0_22, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.54  fof(c_0_23, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.37/0.54  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.37/0.54  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.54  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.54  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.54  fof(c_0_28, plain, ![X24, X25, X26]:(((r2_hidden(X24,X26)|~r1_tarski(k2_tarski(X24,X25),X26))&(r2_hidden(X25,X26)|~r1_tarski(k2_tarski(X24,X25),X26)))&(~r2_hidden(X24,X26)|~r2_hidden(X25,X26)|r1_tarski(k2_tarski(X24,X25),X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.37/0.54  cnf(c_0_29, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.37/0.54  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk1_0,k1_tarski(esk2_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.54  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.37/0.54  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.54  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_24, c_0_19])).
% 0.37/0.54  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.54  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 0.37/0.54  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.37/0.54  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.54  cnf(c_0_39, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.54  cnf(c_0_40, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_29])).
% 0.37/0.54  cnf(c_0_41, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_19]), c_0_33])).
% 0.37/0.54  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.37/0.54  cnf(c_0_43, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.37/0.54  fof(c_0_44, plain, ![X6, X7, X8]:(((~r2_hidden(X6,X7)|~r2_hidden(X6,X8)|~r2_hidden(X6,k5_xboole_0(X7,X8)))&(r2_hidden(X6,X7)|r2_hidden(X6,X8)|~r2_hidden(X6,k5_xboole_0(X7,X8))))&((~r2_hidden(X6,X7)|r2_hidden(X6,X8)|r2_hidden(X6,k5_xboole_0(X7,X8)))&(~r2_hidden(X6,X8)|r2_hidden(X6,X7)|r2_hidden(X6,k5_xboole_0(X7,X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.37/0.54  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_32]), c_0_33])).
% 0.37/0.54  cnf(c_0_46, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.37/0.54  cnf(c_0_47, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.37/0.54  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk1_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_41]), c_0_35]), c_0_42])).
% 0.37/0.54  cnf(c_0_49, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_43]), c_0_34])).
% 0.37/0.54  cnf(c_0_50, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.54  cnf(c_0_51, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.54  cnf(c_0_52, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.37/0.54  cnf(c_0_53, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 0.37/0.54  cnf(c_0_54, negated_conjecture, (k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0))=k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_48])).
% 0.37/0.54  cnf(c_0_55, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_43, c_0_49])).
% 0.37/0.54  cnf(c_0_56, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_32]), c_0_33])).
% 0.37/0.54  cnf(c_0_57, plain, (r2_hidden(X1,k5_xboole_0(k2_enumset1(X2,X2,X2,X1),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.37/0.54  cnf(c_0_58, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_40])).
% 0.37/0.54  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.54  cnf(c_0_60, negated_conjecture, (r1_tarski(k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.37/0.54  cnf(c_0_61, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X2),X4))|r2_hidden(X2,X4)|~r2_hidden(X1,k5_xboole_0(k2_enumset1(X3,X3,X3,X2),X4))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.37/0.54  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_35])).
% 0.37/0.54  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)|~r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.37/0.54  cnf(c_0_64, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X1),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_57])).
% 0.37/0.54  cnf(c_0_65, negated_conjecture, (k5_xboole_0(esk1_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_48])).
% 0.37/0.54  cnf(c_0_66, negated_conjecture, (esk1_0!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.54  cnf(c_0_67, negated_conjecture, (k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_48]), c_0_35]), c_0_48])).
% 0.37/0.54  cnf(c_0_68, negated_conjecture, (k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)|r2_hidden(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.37/0.54  cnf(c_0_69, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.54  cnf(c_0_70, negated_conjecture, (r1_tarski(esk1_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_48]), c_0_65])])).
% 0.37/0.54  cnf(c_0_71, negated_conjecture, (esk1_0!=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_31]), c_0_32]), c_0_33])).
% 0.37/0.54  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.54  cnf(c_0_73, negated_conjecture, (r2_hidden(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_55]), c_0_69])).
% 0.37/0.54  cnf(c_0_74, negated_conjecture, (~r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_70]), c_0_71])).
% 0.37/0.54  cnf(c_0_75, negated_conjecture, (~r2_hidden(esk2_0,k5_xboole_0(X1,esk1_0))|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.37/0.54  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_67]), c_0_74])).
% 0.37/0.54  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk2_0,k5_xboole_0(k2_enumset1(X1,X1,X1,esk2_0),esk1_0))), inference(spm,[status(thm)],[c_0_75, c_0_52])).
% 0.37/0.54  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_76, c_0_77]), ['proof']).
% 0.37/0.54  # SZS output end CNFRefutation
% 0.37/0.54  # Proof object total steps             : 79
% 0.37/0.54  # Proof object clause steps            : 54
% 0.37/0.54  # Proof object formula steps           : 25
% 0.37/0.54  # Proof object conjectures             : 22
% 0.37/0.54  # Proof object clause conjectures      : 19
% 0.37/0.54  # Proof object formula conjectures     : 3
% 0.37/0.54  # Proof object initial clauses used    : 18
% 0.37/0.54  # Proof object initial formulas used   : 12
% 0.37/0.54  # Proof object generating inferences   : 23
% 0.37/0.54  # Proof object simplifying inferences  : 36
% 0.37/0.54  # Training examples: 0 positive, 0 negative
% 0.37/0.54  # Parsed axioms                        : 12
% 0.37/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.54  # Initial clauses                      : 22
% 0.37/0.54  # Removed in clause preprocessing      : 4
% 0.37/0.54  # Initial clauses in saturation        : 18
% 0.37/0.54  # Processed clauses                    : 1837
% 0.37/0.54  # ...of these trivial                  : 97
% 0.37/0.54  # ...subsumed                          : 1365
% 0.37/0.54  # ...remaining for further processing  : 375
% 0.37/0.54  # Other redundant clauses eliminated   : 9
% 0.37/0.54  # Clauses deleted for lack of memory   : 0
% 0.37/0.54  # Backward-subsumed                    : 5
% 0.37/0.54  # Backward-rewritten                   : 99
% 0.37/0.54  # Generated clauses                    : 7757
% 0.37/0.54  # ...of the previous two non-trivial   : 5244
% 0.37/0.54  # Contextual simplify-reflections      : 2
% 0.37/0.54  # Paramodulations                      : 7745
% 0.37/0.54  # Factorizations                       : 2
% 0.37/0.54  # Equation resolutions                 : 9
% 0.37/0.54  # Propositional unsat checks           : 0
% 0.37/0.54  #    Propositional check models        : 0
% 0.37/0.54  #    Propositional check unsatisfiable : 0
% 0.37/0.54  #    Propositional clauses             : 0
% 0.37/0.54  #    Propositional clauses after purity: 0
% 0.37/0.54  #    Propositional unsat core size     : 0
% 0.37/0.54  #    Propositional preprocessing time  : 0.000
% 0.37/0.54  #    Propositional encoding time       : 0.000
% 0.37/0.54  #    Propositional solver time         : 0.000
% 0.37/0.54  #    Success case prop preproc time    : 0.000
% 0.37/0.54  #    Success case prop encoding time   : 0.000
% 0.37/0.54  #    Success case prop solver time     : 0.000
% 0.37/0.54  # Current number of processed clauses  : 250
% 0.37/0.54  #    Positive orientable unit clauses  : 43
% 0.37/0.54  #    Positive unorientable unit clauses: 2
% 0.37/0.54  #    Negative unit clauses             : 67
% 0.37/0.54  #    Non-unit-clauses                  : 138
% 0.37/0.54  # Current number of unprocessed clauses: 3423
% 0.37/0.54  # ...number of literals in the above   : 8263
% 0.37/0.54  # Current number of archived formulas  : 0
% 0.37/0.54  # Current number of archived clauses   : 126
% 0.37/0.54  # Clause-clause subsumption calls (NU) : 15313
% 0.37/0.54  # Rec. Clause-clause subsumption calls : 13639
% 0.37/0.54  # Non-unit clause-clause subsumptions  : 783
% 0.37/0.54  # Unit Clause-clause subsumption calls : 1671
% 0.37/0.54  # Rewrite failures with RHS unbound    : 0
% 0.37/0.54  # BW rewrite match attempts            : 126
% 0.37/0.54  # BW rewrite match successes           : 37
% 0.37/0.54  # Condensation attempts                : 0
% 0.37/0.54  # Condensation successes               : 0
% 0.37/0.54  # Termbank termtop insertions          : 638252
% 0.37/0.54  
% 0.37/0.54  # -------------------------------------------------
% 0.37/0.54  # User time                : 0.197 s
% 0.37/0.54  # System time              : 0.005 s
% 0.37/0.54  # Total time               : 0.202 s
% 0.37/0.54  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
