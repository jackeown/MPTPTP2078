%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 (1164 expanded)
%              Number of clauses        :   44 ( 447 expanded)
%              Number of leaves         :   13 ( 355 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 (1359 expanded)
%              Number of equality atoms :   60 (1154 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t72_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X13,X14] : k3_xboole_0(X13,X14) = k5_xboole_0(k5_xboole_0(X13,X14),k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
      <=> ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t72_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k4_xboole_0(X8,X9) = X8 )
      & ( k4_xboole_0(X8,X9) != X8
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_22,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0)
      | r2_hidden(esk1_0,esk3_0)
      | r2_hidden(esk2_0,esk3_0) )
    & ( ~ r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0) )
    & ( ~ r2_hidden(esk2_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X10,X11,X12] : k5_xboole_0(k5_xboole_0(X10,X11),X12) = k5_xboole_0(X10,k5_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_34,plain,(
    ! [X36,X37,X38] :
      ( r2_hidden(X36,X37)
      | r2_hidden(X38,X37)
      | r1_xboole_0(k2_tarski(X36,X38),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_tarski(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0)
    | k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_17]),c_0_17]),c_0_30]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(X3,X2)
    | r2_hidden(X1,X2)
    | r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_17]),c_0_25]),c_0_26]),c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)))) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_17]),c_0_17]),c_0_30]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r2_hidden(esk1_0,esk3_0)
    | k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_49,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k4_enumset1(X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_17]),c_0_17]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_32]),c_0_32])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(X3,k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),X3))))) = k4_enumset1(X1,X1,X1,X1,X1,X2)
    | r2_hidden(X1,X3)
    | r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)))) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_17]),c_0_17]),c_0_30]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))) != X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))))) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0)
    | k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(X3,k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,k4_enumset1(X1,X1,X1,X1,X1,X2)))))) = k4_enumset1(X1,X1,X1,X1,X1,X2)
    | r2_hidden(X2,X3)
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))))) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_38])).

fof(c_0_57,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_xboole_0(k2_tarski(X33,X34),X35)
      | ~ r2_hidden(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))) != X1 ),
    inference(rw,[status(thm)],[c_0_52,c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_62,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))))) != X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))) = k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_17]),c_0_25]),c_0_26]),c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_49])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_60,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.19/0.39  # and selection function SelectCQIArNpEqFirst.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.027 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(t72_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.19/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.39  fof(t57_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.19/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.39  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.19/0.39  fof(c_0_13, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.39  fof(c_0_14, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_15, plain, ![X13, X14]:k3_xboole_0(X13,X14)=k5_xboole_0(k5_xboole_0(X13,X14),k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.39  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  fof(c_0_18, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_19, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3))))), inference(assume_negation,[status(cth)],[t72_zfmisc_1])).
% 0.19/0.39  fof(c_0_21, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k4_xboole_0(X8,X9)=X8)&(k4_xboole_0(X8,X9)!=X8|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.39  fof(c_0_22, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.39  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.39  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  fof(c_0_27, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.39  fof(c_0_28, negated_conjecture, ((k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk1_0,esk2_0)|(r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)))&((~r2_hidden(esk1_0,esk3_0)|k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0))&(~r2_hidden(esk2_0,esk3_0)|k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).
% 0.19/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.39  cnf(c_0_32, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  fof(c_0_33, plain, ![X10, X11, X12]:k5_xboole_0(k5_xboole_0(X10,X11),X12)=k5_xboole_0(X10,k5_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.39  fof(c_0_34, plain, ![X36, X37, X38]:(r2_hidden(X36,X37)|r2_hidden(X38,X37)|r1_xboole_0(k2_tarski(X36,X38),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)|k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  fof(c_0_36, plain, ![X15, X16]:k2_tarski(X15,X16)=k2_tarski(X16,X15), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.39  cnf(c_0_37, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.19/0.39  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_39, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0)|~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)|k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_17]), c_0_17]), c_0_30]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.19/0.39  cnf(c_0_42, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_43, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.39  cnf(c_0_44, plain, (r2_hidden(X3,X2)|r2_hidden(X1,X2)|r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_17]), c_0_25]), c_0_26]), c_0_32])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0)|~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_17]), c_0_17]), c_0_30]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r2_hidden(esk1_0,esk3_0)|k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_41, c_0_38])).
% 0.19/0.39  cnf(c_0_49, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k4_enumset1(X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_17]), c_0_17]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_32]), c_0_32])).
% 0.19/0.39  cnf(c_0_50, plain, (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(X3,k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),X3)))))=k4_enumset1(X1,X1,X1,X1,X1,X2)|r2_hidden(X1,X3)|r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_17]), c_0_17]), c_0_30]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.19/0.39  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))!=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_30]), c_0_31]), c_0_32])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)))))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_47, c_0_38])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)|k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_55, plain, (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k5_xboole_0(X3,k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,k4_enumset1(X1,X1,X1,X1,X1,X2))))))=k4_enumset1(X1,X1,X1,X1,X1,X2)|r2_hidden(X2,X3)|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)))))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_51, c_0_38])).
% 0.19/0.39  fof(c_0_57, plain, ![X33, X34, X35]:(~r1_xboole_0(k2_tarski(X33,X34),X35)|~r2_hidden(X33,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.19/0.39  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))))!=X1), inference(rw,[status(thm)],[c_0_52, c_0_38])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_53, c_0_49])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_56, c_0_49])).
% 0.19/0.39  cnf(c_0_62, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.39  cnf(c_0_63, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)))))!=X1), inference(spm,[status(thm)],[c_0_58, c_0_49])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))))=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.19/0.39  cnf(c_0_65, plain, (~r2_hidden(X1,X3)|~r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_17]), c_0_25]), c_0_26]), c_0_32])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (r1_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.39  cnf(c_0_67, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X1),X2)), inference(spm,[status(thm)],[c_0_65, c_0_49])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_66])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_60, c_0_68]), c_0_69]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 71
% 0.19/0.39  # Proof object clause steps            : 44
% 0.19/0.39  # Proof object formula steps           : 27
% 0.19/0.39  # Proof object conjectures             : 21
% 0.19/0.39  # Proof object clause conjectures      : 18
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 13
% 0.19/0.39  # Proof object generating inferences   : 9
% 0.19/0.39  # Proof object simplifying inferences  : 91
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 13
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 16
% 0.19/0.39  # Removed in clause preprocessing      : 7
% 0.19/0.39  # Initial clauses in saturation        : 9
% 0.19/0.39  # Processed clauses                    : 126
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 79
% 0.19/0.39  # ...remaining for further processing  : 46
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 5
% 0.19/0.39  # Generated clauses                    : 402
% 0.19/0.39  # ...of the previous two non-trivial   : 401
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 401
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 30
% 0.19/0.39  #    Positive orientable unit clauses  : 3
% 0.19/0.39  #    Positive unorientable unit clauses: 1
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 24
% 0.19/0.39  # Current number of unprocessed clauses: 293
% 0.19/0.39  # ...number of literals in the above   : 812
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 23
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 815
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 814
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 81
% 0.19/0.39  # Unit Clause-clause subsumption calls : 2
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 11
% 0.19/0.39  # BW rewrite match successes           : 11
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 14742
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.041 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.045 s
% 0.19/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
