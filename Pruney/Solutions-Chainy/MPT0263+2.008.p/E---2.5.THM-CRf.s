%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 487 expanded)
%              Number of clauses        :   45 ( 216 expanded)
%              Number of leaves         :   11 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  175 ( 926 expanded)
%              Number of equality atoms :  105 ( 625 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(k1_tarski(X1),X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(k1_tarski(X1),X2)
        | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t58_zfmisc_1])).

fof(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk4_0),esk5_0)
    & k3_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X42,X43] :
      ( ( r2_hidden(esk3_2(X42,X43),X42)
        | X42 = k1_tarski(X43)
        | X42 = k1_xboole_0 )
      & ( esk3_2(X42,X43) != X43
        | X42 = k1_tarski(X43)
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ( ~ r1_xboole_0(X17,X18)
        | k3_xboole_0(X17,X18) = k1_xboole_0 )
      & ( k3_xboole_0(X17,X18) != k1_xboole_0
        | r1_xboole_0(X17,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_22]),c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k3_xboole_0(X19,X20)) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k4_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(X1,esk4_0),X1)
    | k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)) != X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X25
        | X29 = X26
        | X29 = X27
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X25
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X26
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( esk2_4(X31,X32,X33,X34) != X31
        | ~ r2_hidden(esk2_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk2_4(X31,X32,X33,X34) != X32
        | ~ r2_hidden(esk2_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk2_4(X31,X32,X33,X34) != X33
        | ~ r2_hidden(esk2_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( r2_hidden(esk2_4(X31,X32,X33,X34),X34)
        | esk2_4(X31,X32,X33,X34) = X31
        | esk2_4(X31,X32,X33,X34) = X32
        | esk2_4(X31,X32,X33,X34) = X33
        | X34 = k1_enumset1(X31,X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk5_0,X1) = k1_xboole_0
    | r2_hidden(esk3_2(k4_xboole_0(esk5_0,X1),esk4_0),k4_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | r2_hidden(esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)),esk4_0),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_21])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk4_0),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_46])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_56,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk3_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0
    | ~ r2_hidden(X3,k2_enumset1(X4,X4,X4,X4)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_54])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_61,negated_conjecture,
    ( esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk3_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_31])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.40  # and selection function SelectNegativeLiterals.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.027 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.40  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.20/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.40  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.40  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.20/0.40  fof(c_0_12, negated_conjecture, (~r1_xboole_0(k1_tarski(esk4_0),esk5_0)&k3_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.40  fof(c_0_13, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_14, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_15, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_16, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.40  fof(c_0_17, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (k3_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_24, plain, ![X42, X43]:((r2_hidden(esk3_2(X42,X43),X42)|(X42=k1_tarski(X43)|X42=k1_xboole_0))&(esk3_2(X42,X43)!=X43|(X42=k1_tarski(X43)|X42=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.20/0.40  fof(c_0_25, plain, ![X17, X18]:((~r1_xboole_0(X17,X18)|k3_xboole_0(X17,X18)=k1_xboole_0)&(k3_xboole_0(X17,X18)!=k1_xboole_0|r1_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_22])).
% 0.20/0.40  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_22]), c_0_22])).
% 0.20/0.40  cnf(c_0_28, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  fof(c_0_29, plain, ![X19, X20]:k4_xboole_0(X19,k3_xboole_0(X19,X20))=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.40  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.40  cnf(c_0_32, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.40  cnf(c_0_33, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  fof(c_0_34, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.40  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_22])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_2(X1,esk4_0),X1)|k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1))!=X1), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.40  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_22])).
% 0.20/0.40  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  fof(c_0_39, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X29,X28)|(X29=X25|X29=X26|X29=X27)|X28!=k1_enumset1(X25,X26,X27))&(((X30!=X25|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))&(X30!=X26|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27)))&(X30!=X27|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))))&((((esk2_4(X31,X32,X33,X34)!=X31|~r2_hidden(esk2_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33))&(esk2_4(X31,X32,X33,X34)!=X32|~r2_hidden(esk2_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(esk2_4(X31,X32,X33,X34)!=X33|~r2_hidden(esk2_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(r2_hidden(esk2_4(X31,X32,X33,X34),X34)|(esk2_4(X31,X32,X33,X34)=X31|esk2_4(X31,X32,X33,X34)=X32|esk2_4(X31,X32,X33,X34)=X33)|X34=k1_enumset1(X31,X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.40  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (~r1_xboole_0(k1_tarski(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk5_0,X1)=k1_xboole_0|r2_hidden(esk3_2(k4_xboole_0(esk5_0,X1),esk4_0),k4_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  cnf(c_0_44, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_45, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (r1_xboole_0(X1,esk5_0)|r2_hidden(esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)),esk4_0),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.40  cnf(c_0_49, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.20/0.40  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_51, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_21])).
% 0.20/0.40  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_27])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk4_0),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.40  cnf(c_0_54, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_46])).
% 0.20/0.40  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_50, c_0_21])).
% 0.20/0.40  cnf(c_0_56, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.40  cnf(c_0_58, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk3_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_59, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0|~r2_hidden(X3,k2_enumset1(X4,X4,X4,X4))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_32]), c_0_54])).
% 0.20/0.40  cnf(c_0_60, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (esk3_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.40  cnf(c_0_62, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk3_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.40  cnf(c_0_63, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[c_0_53, c_0_61])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_31])).
% 0.20/0.40  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_54, c_0_63])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_66]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 68
% 0.20/0.40  # Proof object clause steps            : 45
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 17
% 0.20/0.40  # Proof object clause conjectures      : 14
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 15
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 13
% 0.20/0.40  # Proof object simplifying inferences  : 35
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 12
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 28
% 0.20/0.40  # Removed in clause preprocessing      : 4
% 0.20/0.40  # Initial clauses in saturation        : 24
% 0.20/0.40  # Processed clauses                    : 348
% 0.20/0.40  # ...of these trivial                  : 17
% 0.20/0.40  # ...subsumed                          : 192
% 0.20/0.40  # ...remaining for further processing  : 139
% 0.20/0.40  # Other redundant clauses eliminated   : 110
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 42
% 0.20/0.40  # Generated clauses                    : 1876
% 0.20/0.40  # ...of the previous two non-trivial   : 1455
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 1761
% 0.20/0.40  # Factorizations                       : 8
% 0.20/0.40  # Equation resolutions                 : 110
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 66
% 0.20/0.40  #    Positive orientable unit clauses  : 18
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 42
% 0.20/0.40  # Current number of unprocessed clauses: 1077
% 0.20/0.40  # ...number of literals in the above   : 3303
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 70
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 352
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 312
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 61
% 0.20/0.40  # Unit Clause-clause subsumption calls : 127
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 87
% 0.20/0.40  # BW rewrite match successes           : 39
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 23036
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.058 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
