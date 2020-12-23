%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:18 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 714 expanded)
%              Number of clauses        :   53 ( 341 expanded)
%              Number of leaves         :   11 ( 185 expanded)
%              Depth                    :   14
%              Number of atoms          :  159 (2196 expanded)
%              Number of equality atoms :   86 ( 968 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t140_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_20,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_21,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_22,c_0_14])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    inference(assume_negation,[status(cth)],[t140_zfmisc_1])).

cnf(c_0_28,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X2))
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = X1
    | ~ r2_hidden(esk1_3(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)),X1),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    & k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk3_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_32,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k5_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_35,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_36,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_37,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X23
        | X24 != k1_tarski(X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_tarski(X23) )
      & ( ~ r2_hidden(esk2_2(X27,X28),X28)
        | esk2_2(X27,X28) != X27
        | X28 = k1_tarski(X27) )
      & ( r2_hidden(esk2_2(X27,X28),X28)
        | esk2_2(X27,X28) = X27
        | X28 = k1_tarski(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X3,k3_xboole_0(X3,X3))
    | ~ r2_hidden(esk1_3(X3,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_28])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk3_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_49,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X2))
    | ~ r2_hidden(esk1_3(X2,X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X1)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_52,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))))) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_14]),c_0_14]),c_0_14]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_45]),c_0_45]),c_0_14]),c_0_14])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_43]),c_0_44]),c_0_46])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X3,k3_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X3,k3_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)
    | r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_59,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X2))
    | ~ r2_hidden(esk1_3(X2,X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,X3))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k3_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_45]),c_0_45]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,k5_xboole_0(X1,k3_xboole_0(X1,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_28])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_45]),c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_54])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),X3))
    | esk1_3(k2_enumset1(X2,X2,X2,X2),X3,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X2 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_65]),c_0_66])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_65]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_71]),c_0_72])]),c_0_73])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_74]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:14:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.73/0.91  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.73/0.91  # and selection function SelectUnlessUniqMax.
% 0.73/0.91  #
% 0.73/0.91  # Preprocessing time       : 0.027 s
% 0.73/0.91  # Presaturation interreduction done
% 0.73/0.91  
% 0.73/0.91  # Proof found!
% 0.73/0.91  # SZS status Theorem
% 0.73/0.91  # SZS output start CNFRefutation
% 0.73/0.91  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.73/0.91  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.73/0.91  fof(t140_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 0.73/0.91  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.73/0.91  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.73/0.91  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.73/0.91  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.73/0.91  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.73/0.91  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.73/0.91  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.73/0.91  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.73/0.91  fof(c_0_11, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.73/0.91  fof(c_0_12, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.73/0.91  cnf(c_0_13, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.73/0.91  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.73/0.91  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.73/0.91  cnf(c_0_16, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.73/0.91  cnf(c_0_17, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.73/0.91  cnf(c_0_18, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.73/0.91  cnf(c_0_19, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.73/0.91  cnf(c_0_20, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_16, c_0_14])).
% 0.73/0.91  cnf(c_0_21, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_17])).
% 0.73/0.91  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.73/0.91  cnf(c_0_23, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_18, c_0_14])).
% 0.73/0.91  cnf(c_0_24, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_19])).
% 0.73/0.91  cnf(c_0_25, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.73/0.91  cnf(c_0_26, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_22, c_0_14])).
% 0.73/0.91  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2)), inference(assume_negation,[status(cth)],[t140_zfmisc_1])).
% 0.73/0.91  cnf(c_0_28, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X2))|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_17])).
% 0.73/0.91  cnf(c_0_29, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=X1|~r2_hidden(esk1_3(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)),X1),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.73/0.91  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_26])).
% 0.73/0.91  fof(c_0_31, negated_conjecture, (r2_hidden(esk3_0,esk4_0)&k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk3_0))!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.73/0.91  fof(c_0_32, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.73/0.91  fof(c_0_33, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.73/0.91  fof(c_0_34, plain, ![X21, X22]:k2_xboole_0(X21,X22)=k5_xboole_0(X21,k4_xboole_0(X22,X21)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.73/0.91  fof(c_0_35, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.73/0.91  fof(c_0_36, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.73/0.91  fof(c_0_37, plain, ![X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X25,X24)|X25=X23|X24!=k1_tarski(X23))&(X26!=X23|r2_hidden(X26,X24)|X24!=k1_tarski(X23)))&((~r2_hidden(esk2_2(X27,X28),X28)|esk2_2(X27,X28)!=X27|X28=k1_tarski(X27))&(r2_hidden(esk2_2(X27,X28),X28)|esk2_2(X27,X28)=X27|X28=k1_tarski(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.73/0.91  cnf(c_0_38, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k5_xboole_0(X3,k3_xboole_0(X3,X3))|~r2_hidden(esk1_3(X3,X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_24, c_0_28])).
% 0.73/0.91  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.73/0.91  cnf(c_0_40, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))=k5_xboole_0(X1,k3_xboole_0(X1,X2))|~r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.73/0.91  cnf(c_0_41, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.73/0.91  cnf(c_0_42, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk3_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.73/0.91  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.73/0.91  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.73/0.91  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.73/0.91  cnf(c_0_46, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.73/0.91  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.73/0.91  fof(c_0_48, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.73/0.91  cnf(c_0_49, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.73/0.91  cnf(c_0_50, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X2))|~r2_hidden(esk1_3(X2,X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.73/0.91  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X1)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.73/0.91  fof(c_0_52, plain, ![X16]:k2_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.73/0.91  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_14]), c_0_14]), c_0_14]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.73/0.91  cnf(c_0_54, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_45]), c_0_45]), c_0_14]), c_0_14])).
% 0.73/0.91  cnf(c_0_55, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.73/0.91  cnf(c_0_56, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_43]), c_0_44]), c_0_46])).
% 0.73/0.91  cnf(c_0_57, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k5_xboole_0(X3,k3_xboole_0(X3,X4))|r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.73/0.91  cnf(c_0_58, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k5_xboole_0(X3,k3_xboole_0(X3,X4))|r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)|r2_hidden(esk1_3(X3,X4,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_30, c_0_17])).
% 0.73/0.91  cnf(c_0_59, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X2))|~r2_hidden(esk1_3(X2,X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,X3)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.73/0.91  cnf(c_0_60, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.73/0.91  cnf(c_0_61, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k3_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))!=esk4_0), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.73/0.91  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_45]), c_0_45]), c_0_14]), c_0_14]), c_0_14])).
% 0.73/0.91  cnf(c_0_63, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_56])).
% 0.73/0.91  cnf(c_0_64, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k5_xboole_0(X2,k3_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,k5_xboole_0(X1,k3_xboole_0(X1,X1))),X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.73/0.91  cnf(c_0_65, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k5_xboole_0(X2,k3_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_59, c_0_28])).
% 0.73/0.91  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_45]), c_0_14])).
% 0.73/0.91  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_54])).
% 0.73/0.91  cnf(c_0_68, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),X3))|esk1_3(k2_enumset1(X2,X2,X2,X2),X3,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X2), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.73/0.91  cnf(c_0_69, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_65]), c_0_66])).
% 0.73/0.91  cnf(c_0_70, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_51])).
% 0.73/0.91  cnf(c_0_71, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.73/0.91  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.73/0.91  cnf(c_0_73, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_65]), c_0_70])).
% 0.73/0.91  cnf(c_0_74, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_71]), c_0_72])]), c_0_73])).
% 0.73/0.91  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_74]), c_0_69])]), ['proof']).
% 0.73/0.91  # SZS output end CNFRefutation
% 0.73/0.91  # Proof object total steps             : 76
% 0.73/0.91  # Proof object clause steps            : 53
% 0.73/0.91  # Proof object formula steps           : 23
% 0.73/0.91  # Proof object conjectures             : 11
% 0.73/0.91  # Proof object clause conjectures      : 8
% 0.73/0.91  # Proof object formula conjectures     : 3
% 0.73/0.91  # Proof object initial clauses used    : 16
% 0.73/0.91  # Proof object initial formulas used   : 11
% 0.73/0.91  # Proof object generating inferences   : 22
% 0.73/0.91  # Proof object simplifying inferences  : 47
% 0.73/0.91  # Training examples: 0 positive, 0 negative
% 0.73/0.91  # Parsed axioms                        : 11
% 0.73/0.91  # Removed by relevancy pruning/SinE    : 0
% 0.73/0.91  # Initial clauses                      : 20
% 0.73/0.91  # Removed in clause preprocessing      : 5
% 0.73/0.91  # Initial clauses in saturation        : 15
% 0.73/0.91  # Processed clauses                    : 3147
% 0.73/0.91  # ...of these trivial                  : 91
% 0.73/0.91  # ...subsumed                          : 2625
% 0.73/0.91  # ...remaining for further processing  : 431
% 0.73/0.91  # Other redundant clauses eliminated   : 64
% 0.73/0.91  # Clauses deleted for lack of memory   : 0
% 0.73/0.91  # Backward-subsumed                    : 25
% 0.73/0.91  # Backward-rewritten                   : 17
% 0.73/0.91  # Generated clauses                    : 33387
% 0.73/0.91  # ...of the previous two non-trivial   : 28407
% 0.73/0.91  # Contextual simplify-reflections      : 5
% 0.73/0.91  # Paramodulations                      : 33211
% 0.73/0.91  # Factorizations                       : 113
% 0.73/0.91  # Equation resolutions                 : 64
% 0.73/0.91  # Propositional unsat checks           : 0
% 0.73/0.91  #    Propositional check models        : 0
% 0.73/0.91  #    Propositional check unsatisfiable : 0
% 0.73/0.91  #    Propositional clauses             : 0
% 0.73/0.91  #    Propositional clauses after purity: 0
% 0.73/0.91  #    Propositional unsat core size     : 0
% 0.73/0.91  #    Propositional preprocessing time  : 0.000
% 0.73/0.91  #    Propositional encoding time       : 0.000
% 0.73/0.91  #    Propositional solver time         : 0.000
% 0.73/0.91  #    Success case prop preproc time    : 0.000
% 0.73/0.91  #    Success case prop encoding time   : 0.000
% 0.73/0.91  #    Success case prop solver time     : 0.000
% 0.73/0.91  # Current number of processed clauses  : 369
% 0.73/0.91  #    Positive orientable unit clauses  : 31
% 0.73/0.91  #    Positive unorientable unit clauses: 5
% 0.73/0.91  #    Negative unit clauses             : 11
% 0.73/0.91  #    Non-unit-clauses                  : 322
% 0.73/0.91  # Current number of unprocessed clauses: 24884
% 0.73/0.91  # ...number of literals in the above   : 113856
% 0.73/0.91  # Current number of archived formulas  : 0
% 0.73/0.91  # Current number of archived clauses   : 62
% 0.73/0.91  # Clause-clause subsumption calls (NU) : 32011
% 0.73/0.91  # Rec. Clause-clause subsumption calls : 15471
% 0.73/0.91  # Non-unit clause-clause subsumptions  : 1113
% 0.73/0.91  # Unit Clause-clause subsumption calls : 1601
% 0.73/0.91  # Rewrite failures with RHS unbound    : 853
% 0.73/0.91  # BW rewrite match attempts            : 625
% 0.73/0.91  # BW rewrite match successes           : 49
% 0.73/0.91  # Condensation attempts                : 0
% 0.73/0.91  # Condensation successes               : 0
% 0.73/0.91  # Termbank termtop insertions          : 1152395
% 0.73/0.91  
% 0.73/0.91  # -------------------------------------------------
% 0.73/0.91  # User time                : 0.559 s
% 0.73/0.91  # System time              : 0.014 s
% 0.73/0.91  # Total time               : 0.574 s
% 0.73/0.91  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
