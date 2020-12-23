%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:09 EST 2020

% Result     : Theorem 27.62s
% Output     : CNFRefutation 27.62s
% Verified   : 
% Statistics : Number of formulae       :   66 (1164 expanded)
%              Number of clauses        :   49 ( 557 expanded)
%              Number of leaves         :    8 ( 283 expanded)
%              Depth                    :   15
%              Number of atoms          :  198 (3876 expanded)
%              Number of equality atoms :   93 (2106 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t60_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X27
        | X30 = X28
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X27
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( esk3_3(X32,X33,X34) != X32
        | ~ r2_hidden(esk3_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( esk3_3(X32,X33,X34) != X33
        | ~ r2_hidden(esk3_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( r2_hidden(esk3_3(X32,X33,X34),X34)
        | esk3_3(X32,X33,X34) = X32
        | esk3_3(X32,X33,X34) = X33
        | X34 = k2_tarski(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X37,X38] : k2_enumset1(X37,X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,X2)
       => ( ( r2_hidden(X3,X2)
            & X1 != X3 )
          | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t60_zfmisc_1])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | esk3_3(X1,X2,X3) = X1
    | esk3_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | X4 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    & ( ~ r2_hidden(esk6_0,esk5_0)
      | esk4_0 = esk6_0 )
    & k3_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_23,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk3_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( esk3_3(X1,X2,X3) = X2
    | esk3_3(X1,X2,X3) = X1
    | X3 = k2_enumset1(X1,X1,X1,X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( X3 = k2_enumset1(X1,X1,X1,X2)
    | esk3_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_33,plain,
    ( X1 = k2_enumset1(X2,X2,X2,X2)
    | esk3_3(X2,X2,X1) = X2
    | r2_hidden(esk3_3(X2,X2,X1),X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0),k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0),esk5_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_16]),c_0_16]),c_0_13])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_13]),c_0_13])).

cnf(c_0_41,plain,
    ( X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk3_3(X2,X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(esk5_0,X1))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_38,c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk5_0,X1) = k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)
    | r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,X1)),k4_xboole_0(esk5_0,X1))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))) = esk6_0
    | esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))) = esk4_0
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 = esk6_0
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_59]),c_0_44])]),c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_63,negated_conjecture,
    ( esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_62]),c_0_62]),c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_63]),c_0_44])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 27.62/27.81  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 27.62/27.81  # and selection function SelectNegativeLiterals.
% 27.62/27.81  #
% 27.62/27.81  # Preprocessing time       : 0.027 s
% 27.62/27.81  # Presaturation interreduction done
% 27.62/27.81  
% 27.62/27.81  # Proof found!
% 27.62/27.81  # SZS status Theorem
% 27.62/27.81  # SZS output start CNFRefutation
% 27.62/27.81  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 27.62/27.81  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 27.62/27.81  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 27.62/27.81  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 27.62/27.81  fof(t60_zfmisc_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 27.62/27.81  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 27.62/27.81  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 27.62/27.81  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.62/27.81  fof(c_0_8, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 27.62/27.81  fof(c_0_9, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 27.62/27.81  fof(c_0_10, plain, ![X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X30,X29)|(X30=X27|X30=X28)|X29!=k2_tarski(X27,X28))&((X31!=X27|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))&(X31!=X28|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))))&(((esk3_3(X32,X33,X34)!=X32|~r2_hidden(esk3_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33))&(esk3_3(X32,X33,X34)!=X33|~r2_hidden(esk3_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33)))&(r2_hidden(esk3_3(X32,X33,X34),X34)|(esk3_3(X32,X33,X34)=X32|esk3_3(X32,X33,X34)=X33)|X34=k2_tarski(X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 27.62/27.81  fof(c_0_11, plain, ![X37, X38]:k2_enumset1(X37,X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 27.62/27.81  cnf(c_0_12, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 27.62/27.81  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 27.62/27.81  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1)))), inference(assume_negation,[status(cth)],[t60_zfmisc_1])).
% 27.62/27.81  cnf(c_0_15, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|esk3_3(X1,X2,X3)=X1|esk3_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 27.62/27.81  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 27.62/27.81  fof(c_0_17, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 27.62/27.81  cnf(c_0_18, plain, (r2_hidden(X1,X4)|X4!=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 27.62/27.81  fof(c_0_19, negated_conjecture, (r2_hidden(esk4_0,esk5_0)&((~r2_hidden(esk6_0,esk5_0)|esk4_0=esk6_0)&k3_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0)!=k1_tarski(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 27.62/27.81  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 27.62/27.81  fof(c_0_21, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 27.62/27.81  fof(c_0_22, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 27.62/27.81  cnf(c_0_23, plain, (X3=k2_tarski(X1,X2)|esk3_3(X1,X2,X3)!=X2|~r2_hidden(esk3_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 27.62/27.81  cnf(c_0_24, plain, (esk3_3(X1,X2,X3)=X2|esk3_3(X1,X2,X3)=X1|X3=k2_enumset1(X1,X1,X1,X2)|r2_hidden(esk3_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 27.62/27.81  cnf(c_0_25, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 27.62/27.81  cnf(c_0_26, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_18])).
% 27.62/27.81  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 27.62/27.81  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[c_0_20, c_0_16])).
% 27.62/27.81  cnf(c_0_29, negated_conjecture, (k3_xboole_0(k2_tarski(esk4_0,esk6_0),esk5_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 27.62/27.81  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 27.62/27.81  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 27.62/27.81  cnf(c_0_32, plain, (X3=k2_enumset1(X1,X1,X1,X2)|esk3_3(X1,X2,X3)!=X2|~r2_hidden(esk3_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[c_0_23, c_0_16])).
% 27.62/27.81  cnf(c_0_33, plain, (X1=k2_enumset1(X2,X2,X2,X2)|esk3_3(X2,X2,X1)=X2|r2_hidden(esk3_3(X2,X2,X1),X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).
% 27.62/27.81  cnf(c_0_34, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_25])).
% 27.62/27.81  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 27.62/27.81  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 27.62/27.81  cnf(c_0_37, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 27.62/27.81  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 27.62/27.81  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0),k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0),esk5_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_16]), c_0_16]), c_0_13])).
% 27.62/27.81  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_13]), c_0_13])).
% 27.62/27.81  cnf(c_0_41, plain, (X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk3_3(X2,X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 27.62/27.81  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(esk5_0,X1))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 27.62/27.81  cnf(c_0_43, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_35])).
% 27.62/27.81  cnf(c_0_44, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,X1))))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 27.62/27.81  cnf(c_0_45, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 27.62/27.81  cnf(c_0_46, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_38, c_0_13])).
% 27.62/27.81  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 27.62/27.81  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk5_0,X1)=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)|r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,X1)),k4_xboole_0(esk5_0,X1))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 27.62/27.81  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk4_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,X1)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 27.62/27.81  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 27.62/27.81  cnf(c_0_51, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_16])).
% 27.62/27.81  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_46])).
% 27.62/27.81  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 27.62/27.81  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_50])).
% 27.62/27.81  cnf(c_0_55, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_51])).
% 27.62/27.81  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 27.62/27.81  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 27.62/27.81  cnf(c_0_58, negated_conjecture, (esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))))=esk6_0|esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))))=esk4_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 27.62/27.81  cnf(c_0_59, negated_conjecture, (esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))))=esk4_0|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 27.62/27.81  cnf(c_0_60, negated_conjecture, (esk4_0=esk6_0|~r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 27.62/27.81  cnf(c_0_61, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_59]), c_0_44])]), c_0_47])).
% 27.62/27.81  cnf(c_0_62, negated_conjecture, (esk6_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 27.62/27.81  cnf(c_0_63, negated_conjecture, (esk3_3(esk4_0,esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_62]), c_0_62]), c_0_62])])).
% 27.62/27.81  cnf(c_0_64, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_47, c_0_62])).
% 27.62/27.81  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_63]), c_0_44])]), c_0_64]), ['proof']).
% 27.62/27.81  # SZS output end CNFRefutation
% 27.62/27.81  # Proof object total steps             : 66
% 27.62/27.81  # Proof object clause steps            : 49
% 27.62/27.81  # Proof object formula steps           : 17
% 27.62/27.81  # Proof object conjectures             : 23
% 27.62/27.81  # Proof object clause conjectures      : 20
% 27.62/27.81  # Proof object formula conjectures     : 3
% 27.62/27.81  # Proof object initial clauses used    : 16
% 27.62/27.81  # Proof object initial formulas used   : 8
% 27.62/27.81  # Proof object generating inferences   : 14
% 27.62/27.81  # Proof object simplifying inferences  : 36
% 27.62/27.81  # Training examples: 0 positive, 0 negative
% 27.62/27.81  # Parsed axioms                        : 8
% 27.62/27.81  # Removed by relevancy pruning/SinE    : 0
% 27.62/27.81  # Initial clauses                      : 25
% 27.62/27.81  # Removed in clause preprocessing      : 3
% 27.62/27.81  # Initial clauses in saturation        : 22
% 27.62/27.81  # Processed clauses                    : 15665
% 27.62/27.81  # ...of these trivial                  : 1212
% 27.62/27.81  # ...subsumed                          : 10396
% 27.62/27.81  # ...remaining for further processing  : 4057
% 27.62/27.81  # Other redundant clauses eliminated   : 1248
% 27.62/27.81  # Clauses deleted for lack of memory   : 183467
% 27.62/27.81  # Backward-subsumed                    : 182
% 27.62/27.81  # Backward-rewritten                   : 224
% 27.62/27.81  # Generated clauses                    : 2305439
% 27.62/27.81  # ...of the previous two non-trivial   : 2244577
% 27.62/27.81  # Contextual simplify-reflections      : 24
% 27.62/27.81  # Paramodulations                      : 2303747
% 27.62/27.81  # Factorizations                       : 445
% 27.62/27.81  # Equation resolutions                 : 1249
% 27.62/27.81  # Propositional unsat checks           : 0
% 27.62/27.81  #    Propositional check models        : 0
% 27.62/27.81  #    Propositional check unsatisfiable : 0
% 27.62/27.81  #    Propositional clauses             : 0
% 27.62/27.81  #    Propositional clauses after purity: 0
% 27.62/27.81  #    Propositional unsat core size     : 0
% 27.62/27.81  #    Propositional preprocessing time  : 0.000
% 27.62/27.81  #    Propositional encoding time       : 0.000
% 27.62/27.81  #    Propositional solver time         : 0.000
% 27.62/27.81  #    Success case prop preproc time    : 0.000
% 27.62/27.81  #    Success case prop encoding time   : 0.000
% 27.62/27.81  #    Success case prop solver time     : 0.000
% 27.62/27.81  # Current number of processed clauses  : 3621
% 27.62/27.81  #    Positive orientable unit clauses  : 670
% 27.62/27.81  #    Positive unorientable unit clauses: 1
% 27.62/27.81  #    Negative unit clauses             : 678
% 27.62/27.81  #    Non-unit-clauses                  : 2272
% 27.62/27.81  # Current number of unprocessed clauses: 1152903
% 27.62/27.81  # ...number of literals in the above   : 5187955
% 27.62/27.81  # Current number of archived formulas  : 0
% 27.62/27.81  # Current number of archived clauses   : 430
% 27.62/27.81  # Clause-clause subsumption calls (NU) : 354469
% 27.62/27.81  # Rec. Clause-clause subsumption calls : 229040
% 27.62/27.81  # Non-unit clause-clause subsumptions  : 6488
% 27.62/27.81  # Unit Clause-clause subsumption calls : 81529
% 27.62/27.81  # Rewrite failures with RHS unbound    : 0
% 27.62/27.81  # BW rewrite match attempts            : 83034
% 27.62/27.81  # BW rewrite match successes           : 168
% 27.62/27.81  # Condensation attempts                : 0
% 27.62/27.81  # Condensation successes               : 0
% 27.62/27.81  # Termbank termtop insertions          : 79805889
% 27.71/27.91  
% 27.71/27.91  # -------------------------------------------------
% 27.71/27.91  # User time                : 26.585 s
% 27.71/27.91  # System time              : 0.980 s
% 27.71/27.91  # Total time               : 27.565 s
% 27.71/27.91  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
