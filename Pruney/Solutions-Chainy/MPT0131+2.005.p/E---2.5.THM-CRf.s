%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:05 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   74 (7437 expanded)
%              Number of clauses        :   59 (3710 expanded)
%              Number of leaves         :    7 (1856 expanded)
%              Depth                    :   18
%              Number of atoms          :  153 (20314 expanded)
%              Number of equality atoms :   49 (9387 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t47_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k5_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_9,plain,(
    ! [X22,X23] : k2_tarski(X22,X23) = k2_xboole_0(k1_tarski(X22),k1_tarski(X23)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X24,X25,X26] : k1_enumset1(X24,X25,X26) = k2_xboole_0(k1_tarski(X24),k2_tarski(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X3 = k5_xboole_0(X1,k4_xboole_0(X2,X1))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_16,plain,(
    ! [X27,X28,X29,X30] : k2_enumset1(X27,X28,X29,X30) = k2_xboole_0(k1_tarski(X27),k1_enumset1(X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_19,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t47_enumset1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X3 != k5_xboole_0(X4,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_11]),c_0_18])).

cnf(c_0_25,plain,
    ( X3 = k5_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1
    | r2_hidden(esk1_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_28,plain,(
    ! [X17,X18,X19,X20,X21] : k3_enumset1(X17,X18,X19,X20,X21) = k2_xboole_0(k1_enumset1(X17,X18,X19),k2_tarski(X20,X21)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

fof(c_0_29,negated_conjecture,(
    k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_11]),c_0_24])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k5_xboole_0(X3,k4_xboole_0(X4,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_11])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X3 != k5_xboole_0(X2,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_11])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | ~ r2_hidden(X1,k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) = k2_enumset1(X1,X2,X3,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_11]),c_0_18]),c_0_24]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_11])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | ~ r2_hidden(X1,k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) = k2_enumset1(X1,X2,X2,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))))
    | r2_hidden(X1,k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))))
    | ~ r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))
    | r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk2_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14])])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X4),k1_tarski(X1))) = k2_enumset1(X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | ~ r2_hidden(X1,k2_enumset1(X4,X5,X5,X5)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))))
    | r2_hidden(X1,k1_tarski(X5))
    | ~ r2_hidden(X1,k2_enumset1(X5,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))
    | r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_45]),c_0_45]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | ~ r2_hidden(X1,k1_tarski(X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))
    | ~ r2_hidden(X1,k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))
    | r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk4_0,esk5_0,esk6_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_45]),c_0_48]),c_0_53])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | ~ r2_hidden(X1,k1_tarski(X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))
    | ~ r2_hidden(X1,k2_enumset1(X5,X6,X6,X6)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))
    | r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk5_0,esk6_0,esk6_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_55]),c_0_33]),c_0_45]),c_0_56])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | ~ r2_hidden(X1,k2_enumset1(X3,X4,X5,X5)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))
    | ~ r2_hidden(X1,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))
    | r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_enumset1(X1,X2,X3,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))
    | r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(X1,esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_55])).

cnf(c_0_63,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))
    | ~ r2_hidden(X1,k2_enumset1(X2,X3,X4,X4)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_61]),c_0_42]),c_0_62])).

cnf(c_0_66,plain,
    ( X3 = k5_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_63,c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_enumset1(esk2_0,esk3_0,esk4_0,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_67]),c_0_42])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_65]),c_0_33]),c_0_45]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_53])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_49])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_70]),c_0_33]),c_0_33]),c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.55/0.77  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.55/0.77  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.55/0.77  #
% 0.55/0.77  # Preprocessing time       : 0.027 s
% 0.55/0.77  # Presaturation interreduction done
% 0.55/0.77  
% 0.55/0.77  # Proof found!
% 0.55/0.77  # SZS status Theorem
% 0.55/0.77  # SZS output start CNFRefutation
% 0.55/0.77  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.55/0.77  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.55/0.77  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.55/0.77  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.55/0.77  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.55/0.77  fof(t47_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.55/0.77  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 0.55/0.77  fof(c_0_7, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(r2_hidden(X9,X6)|r2_hidden(X9,X7))|X8!=k2_xboole_0(X6,X7))&((~r2_hidden(X10,X6)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))&(~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))))&(((~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k2_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.55/0.77  fof(c_0_8, plain, ![X15, X16]:k2_xboole_0(X15,X16)=k5_xboole_0(X15,k4_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.55/0.77  fof(c_0_9, plain, ![X22, X23]:k2_tarski(X22,X23)=k2_xboole_0(k1_tarski(X22),k1_tarski(X23)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.55/0.77  cnf(c_0_10, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.55/0.77  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.55/0.77  fof(c_0_12, plain, ![X24, X25, X26]:k1_enumset1(X24,X25,X26)=k2_xboole_0(k1_tarski(X24),k2_tarski(X25,X26)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.55/0.77  cnf(c_0_13, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.55/0.77  cnf(c_0_14, plain, (X3=k5_xboole_0(X1,k4_xboole_0(X2,X1))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.55/0.77  cnf(c_0_15, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.55/0.77  fof(c_0_16, plain, ![X27, X28, X29, X30]:k2_enumset1(X27,X28,X29,X30)=k2_xboole_0(k1_tarski(X27),k1_enumset1(X28,X29,X30)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.55/0.77  cnf(c_0_17, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.55/0.77  cnf(c_0_18, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_13, c_0_11])).
% 0.55/0.77  cnf(c_0_19, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.55/0.77  cnf(c_0_20, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_14])).
% 0.55/0.77  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(assume_negation,[status(cth)],[t47_enumset1])).
% 0.55/0.77  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X3!=k5_xboole_0(X4,k4_xboole_0(X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_11])).
% 0.55/0.77  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.77  cnf(c_0_24, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_11]), c_0_18])).
% 0.55/0.77  cnf(c_0_25, plain, (X3=k5_xboole_0(X1,k4_xboole_0(X2,X1))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_19, c_0_11])).
% 0.55/0.77  cnf(c_0_26, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1|r2_hidden(esk1_3(X1,X1,X1),X1)), inference(ef,[status(thm)],[c_0_20])).
% 0.55/0.77  cnf(c_0_27, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.55/0.77  fof(c_0_28, plain, ![X17, X18, X19, X20, X21]:k3_enumset1(X17,X18,X19,X20,X21)=k2_xboole_0(k1_enumset1(X17,X18,X19),k2_tarski(X20,X21)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.55/0.77  fof(c_0_29, negated_conjecture, k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.55/0.77  cnf(c_0_30, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.55/0.77  cnf(c_0_31, plain, (r2_hidden(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_22])).
% 0.55/0.77  cnf(c_0_32, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_11]), c_0_24])).
% 0.55/0.77  cnf(c_0_33, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_26])).
% 0.55/0.77  cnf(c_0_34, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k5_xboole_0(X3,k4_xboole_0(X4,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_11])).
% 0.55/0.77  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.55/0.77  cnf(c_0_36, negated_conjecture, (k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.55/0.77  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X3!=k5_xboole_0(X2,k4_xboole_0(X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_11])).
% 0.55/0.77  cnf(c_0_38, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))|~r2_hidden(X1,k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.55/0.77  cnf(c_0_39, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))=k2_enumset1(X1,X2,X3,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.55/0.77  cnf(c_0_40, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_34])).
% 0.55/0.77  cnf(c_0_41, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_11]), c_0_18]), c_0_24]), c_0_24])).
% 0.55/0.77  cnf(c_0_42, negated_conjecture, (k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0)))), inference(rw,[status(thm)],[c_0_36, c_0_11])).
% 0.55/0.77  cnf(c_0_43, plain, (r2_hidden(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.55/0.77  cnf(c_0_44, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))|~r2_hidden(X1,k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))))), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 0.55/0.77  cnf(c_0_45, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))=k2_enumset1(X1,X2,X2,X2)), inference(spm,[status(thm)],[c_0_39, c_0_33])).
% 0.55/0.77  cnf(c_0_46, plain, (r2_hidden(X1,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))))|r2_hidden(X1,k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))))|~r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.55/0.77  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))|r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk2_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_14])])).
% 0.55/0.77  cnf(c_0_48, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X4),k1_tarski(X1)))=k2_enumset1(X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_32, c_0_39])).
% 0.55/0.77  cnf(c_0_49, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))|~r2_hidden(X1,k1_tarski(X2))), inference(spm,[status(thm)],[c_0_43, c_0_32])).
% 0.55/0.77  cnf(c_0_50, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))|~r2_hidden(X1,k2_enumset1(X4,X5,X5,X5))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.55/0.77  cnf(c_0_51, plain, (r2_hidden(X1,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))))|r2_hidden(X1,k1_tarski(X5))|~r2_hidden(X1,k2_enumset1(X5,X2,X3,X4))), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 0.55/0.77  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))|r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_45]), c_0_45]), c_0_48]), c_0_49]), c_0_50])).
% 0.55/0.77  cnf(c_0_53, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))|~r2_hidden(X1,k1_tarski(X3))), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 0.55/0.77  cnf(c_0_54, plain, (r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))|~r2_hidden(X1,k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))))), inference(spm,[status(thm)],[c_0_31, c_0_41])).
% 0.55/0.77  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))|r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk4_0,esk5_0,esk6_0,esk6_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_45]), c_0_48]), c_0_53])).
% 0.55/0.77  cnf(c_0_56, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))|~r2_hidden(X1,k1_tarski(X4))), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.55/0.77  cnf(c_0_57, plain, (r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))|~r2_hidden(X1,k2_enumset1(X5,X6,X6,X6))), inference(spm,[status(thm)],[c_0_54, c_0_45])).
% 0.55/0.77  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))|r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk5_0,esk6_0,esk6_0,esk6_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_55]), c_0_33]), c_0_45]), c_0_56])).
% 0.55/0.77  cnf(c_0_59, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))|~r2_hidden(X1,k2_enumset1(X3,X4,X5,X5))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.55/0.77  cnf(c_0_60, plain, (r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))|~r2_hidden(X1,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))))), inference(spm,[status(thm)],[c_0_43, c_0_41])).
% 0.55/0.77  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))|r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_enumset1(X1,X2,X3,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.55/0.77  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))|r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(X1,esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_59, c_0_55])).
% 0.55/0.77  cnf(c_0_63, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.55/0.77  cnf(c_0_64, plain, (r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X6))|~r2_hidden(X1,k2_enumset1(X2,X3,X4,X4))), inference(spm,[status(thm)],[c_0_60, c_0_39])).
% 0.55/0.77  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk2_0,esk3_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_61]), c_0_42]), c_0_62])).
% 0.55/0.77  cnf(c_0_66, plain, (X3=k5_xboole_0(X1,k4_xboole_0(X2,X1))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_63, c_0_11])).
% 0.55/0.77  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_enumset1(esk2_0,esk3_0,esk4_0,X1,X2))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.55/0.77  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_42])).
% 0.55/0.77  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_67]), c_0_42])).
% 0.55/0.77  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k2_enumset1(esk3_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_65]), c_0_33]), c_0_45]), c_0_68])).
% 0.55/0.77  cnf(c_0_71, negated_conjecture, (~r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_53])).
% 0.55/0.77  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk1_3(k1_tarski(esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_tarski(esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_49])).
% 0.55/0.77  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_70]), c_0_33]), c_0_33]), c_0_71]), c_0_72]), ['proof']).
% 0.55/0.77  # SZS output end CNFRefutation
% 0.55/0.77  # Proof object total steps             : 74
% 0.55/0.77  # Proof object clause steps            : 59
% 0.55/0.77  # Proof object formula steps           : 15
% 0.55/0.77  # Proof object conjectures             : 19
% 0.55/0.77  # Proof object clause conjectures      : 16
% 0.55/0.77  # Proof object formula conjectures     : 3
% 0.55/0.77  # Proof object initial clauses used    : 12
% 0.55/0.77  # Proof object initial formulas used   : 7
% 0.55/0.77  # Proof object generating inferences   : 33
% 0.55/0.77  # Proof object simplifying inferences  : 43
% 0.55/0.77  # Training examples: 0 positive, 0 negative
% 0.55/0.77  # Parsed axioms                        : 7
% 0.55/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.55/0.77  # Initial clauses                      : 12
% 0.55/0.77  # Removed in clause preprocessing      : 3
% 0.55/0.77  # Initial clauses in saturation        : 9
% 0.55/0.77  # Processed clauses                    : 518
% 0.55/0.77  # ...of these trivial                  : 3
% 0.55/0.77  # ...subsumed                          : 268
% 0.55/0.77  # ...remaining for further processing  : 247
% 0.55/0.77  # Other redundant clauses eliminated   : 139
% 0.55/0.77  # Clauses deleted for lack of memory   : 0
% 0.55/0.77  # Backward-subsumed                    : 17
% 0.55/0.77  # Backward-rewritten                   : 4
% 0.55/0.77  # Generated clauses                    : 12098
% 0.55/0.77  # ...of the previous two non-trivial   : 11706
% 0.55/0.77  # Contextual simplify-reflections      : 9
% 0.55/0.77  # Paramodulations                      : 11765
% 0.55/0.77  # Factorizations                       : 186
% 0.55/0.77  # Equation resolutions                 : 139
% 0.55/0.77  # Propositional unsat checks           : 0
% 0.55/0.77  #    Propositional check models        : 0
% 0.55/0.77  #    Propositional check unsatisfiable : 0
% 0.55/0.77  #    Propositional clauses             : 0
% 0.55/0.77  #    Propositional clauses after purity: 0
% 0.55/0.77  #    Propositional unsat core size     : 0
% 0.55/0.77  #    Propositional preprocessing time  : 0.000
% 0.55/0.77  #    Propositional encoding time       : 0.000
% 0.55/0.77  #    Propositional solver time         : 0.000
% 0.55/0.77  #    Success case prop preproc time    : 0.000
% 0.55/0.77  #    Success case prop encoding time   : 0.000
% 0.55/0.77  #    Success case prop solver time     : 0.000
% 0.55/0.77  # Current number of processed clauses  : 206
% 0.55/0.77  #    Positive orientable unit clauses  : 10
% 0.55/0.77  #    Positive unorientable unit clauses: 7
% 0.55/0.77  #    Negative unit clauses             : 7
% 0.55/0.77  #    Non-unit-clauses                  : 182
% 0.55/0.77  # Current number of unprocessed clauses: 11187
% 0.55/0.77  # ...number of literals in the above   : 78700
% 0.55/0.77  # Current number of archived formulas  : 0
% 0.55/0.77  # Current number of archived clauses   : 41
% 0.55/0.77  # Clause-clause subsumption calls (NU) : 21578
% 0.55/0.77  # Rec. Clause-clause subsumption calls : 5688
% 0.55/0.77  # Non-unit clause-clause subsumptions  : 265
% 0.55/0.77  # Unit Clause-clause subsumption calls : 1230
% 0.55/0.77  # Rewrite failures with RHS unbound    : 0
% 0.55/0.77  # BW rewrite match attempts            : 359
% 0.55/0.77  # BW rewrite match successes           : 90
% 0.55/0.77  # Condensation attempts                : 0
% 0.55/0.77  # Condensation successes               : 0
% 0.55/0.77  # Termbank termtop insertions          : 606957
% 0.55/0.77  
% 0.55/0.77  # -------------------------------------------------
% 0.55/0.77  # User time                : 0.412 s
% 0.55/0.77  # System time              : 0.015 s
% 0.55/0.77  # Total time               : 0.427 s
% 0.55/0.77  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
