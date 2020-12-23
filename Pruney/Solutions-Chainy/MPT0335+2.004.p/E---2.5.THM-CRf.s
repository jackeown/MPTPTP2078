%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:40 EST 2020

% Result     : Theorem 17.04s
% Output     : CNFRefutation 17.04s
% Verified   : 
% Statistics : Number of formulae       :   93 (1125 expanded)
%              Number of clauses        :   64 ( 471 expanded)
%              Number of leaves         :   14 ( 318 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 (1806 expanded)
%              Number of equality atoms :  101 (1263 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    & k3_xboole_0(esk6_0,esk7_0) = k1_tarski(esk8_0)
    & r2_hidden(esk8_0,esk5_0)
    & k3_xboole_0(esk5_0,esk7_0) != k1_tarski(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X39
        | X42 = X40
        | X41 != k2_tarski(X39,X40) )
      & ( X43 != X39
        | r2_hidden(X43,X41)
        | X41 != k2_tarski(X39,X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k2_tarski(X39,X40) )
      & ( esk4_3(X44,X45,X46) != X44
        | ~ r2_hidden(esk4_3(X44,X45,X46),X46)
        | X46 = k2_tarski(X44,X45) )
      & ( esk4_3(X44,X45,X46) != X45
        | ~ r2_hidden(esk4_3(X44,X45,X46),X46)
        | X46 = k2_tarski(X44,X45) )
      & ( r2_hidden(esk4_3(X44,X45,X46),X46)
        | esk4_3(X44,X45,X46) = X44
        | esk4_3(X44,X45,X46) = X45
        | X46 = k2_tarski(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X49,X50] : k1_enumset1(X49,X49,X50) = k2_tarski(X49,X50) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X54,X55,X56,X57] : k3_enumset1(X54,X54,X55,X56,X57) = k2_enumset1(X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk8_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X48] : k2_tarski(X48,X48) = k1_tarski(X48) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk7_0) = k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(esk6_0,X1))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)) = k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_28]),c_0_29]),c_0_39]),c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(esk6_0,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_46,plain,(
    ! [X25,X26,X27] : k3_xboole_0(k3_xboole_0(X25,X26),X27) = k3_xboole_0(X25,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_47,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_51,plain,(
    ! [X22] : k3_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_52,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(esk7_0,X1))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_48])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_39]),c_0_39])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_57,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X32
        | X33 != k1_tarski(X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k1_tarski(X32) )
      & ( ~ r2_hidden(esk3_2(X36,X37),X37)
        | esk3_2(X36,X37) != X36
        | X37 = k1_tarski(X36) )
      & ( r2_hidden(esk3_2(X36,X37),X37)
        | esk3_2(X36,X37) = X36
        | X37 = k1_tarski(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(esk7_0,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_53])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_56,c_0_39])).

cnf(c_0_62,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1))))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(esk5_0,X1))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_67,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_38]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(X1,esk7_0)))
    | ~ r2_hidden(esk8_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))
    | r2_hidden(esk8_0,k4_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k4_xboole_0(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_68])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_54])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))) = k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( X1 = esk8_0
    | ~ r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_43])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk7_0) != k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | ~ r2_hidden(esk8_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1)))),X2)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_54]),c_0_54])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)),esk5_0))))) = k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_79])).

cnf(c_0_86,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_87,negated_conjecture,
    ( esk2_3(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))) = esk8_0
    | k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1) = k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)) != k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_38]),c_0_28]),c_0_29]),c_0_39]),c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))))))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_55]),c_0_65]),c_0_55]),c_0_65]),c_0_65]),c_0_54]),c_0_55]),c_0_60]),c_0_55]),c_0_78]),c_0_60]),c_0_55]),c_0_78]),c_0_55]),c_0_65]),c_0_65]),c_0_55]),c_0_65]),c_0_78]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1) = k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))
    | r2_hidden(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_45])])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)) != k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_43])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_76]),c_0_54]),c_0_60]),c_0_61]),c_0_60]),c_0_55]),c_0_78]),c_0_60]),c_0_61]),c_0_60]),c_0_55]),c_0_78]),c_0_91]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:37:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 17.04/17.20  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 17.04/17.20  # and selection function SelectCQArNTNpEqFirst.
% 17.04/17.20  #
% 17.04/17.20  # Preprocessing time       : 0.028 s
% 17.04/17.20  # Presaturation interreduction done
% 17.04/17.20  
% 17.04/17.20  # Proof found!
% 17.04/17.20  # SZS status Theorem
% 17.04/17.20  # SZS output start CNFRefutation
% 17.04/17.20  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 17.04/17.20  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.04/17.20  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.04/17.20  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 17.04/17.20  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 17.04/17.20  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 17.04/17.20  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 17.04/17.20  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 17.04/17.20  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.04/17.20  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 17.04/17.20  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.04/17.20  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 17.04/17.20  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.04/17.20  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 17.04/17.20  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 17.04/17.20  fof(c_0_15, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 17.04/17.20  fof(c_0_16, negated_conjecture, (((r1_tarski(esk5_0,esk6_0)&k3_xboole_0(esk6_0,esk7_0)=k1_tarski(esk8_0))&r2_hidden(esk8_0,esk5_0))&k3_xboole_0(esk5_0,esk7_0)!=k1_tarski(esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 17.04/17.20  fof(c_0_17, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 17.04/17.20  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 17.04/17.20  cnf(c_0_19, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 17.04/17.20  fof(c_0_20, plain, ![X39, X40, X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X42,X41)|(X42=X39|X42=X40)|X41!=k2_tarski(X39,X40))&((X43!=X39|r2_hidden(X43,X41)|X41!=k2_tarski(X39,X40))&(X43!=X40|r2_hidden(X43,X41)|X41!=k2_tarski(X39,X40))))&(((esk4_3(X44,X45,X46)!=X44|~r2_hidden(esk4_3(X44,X45,X46),X46)|X46=k2_tarski(X44,X45))&(esk4_3(X44,X45,X46)!=X45|~r2_hidden(esk4_3(X44,X45,X46),X46)|X46=k2_tarski(X44,X45)))&(r2_hidden(esk4_3(X44,X45,X46),X46)|(esk4_3(X44,X45,X46)=X44|esk4_3(X44,X45,X46)=X45)|X46=k2_tarski(X44,X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 17.04/17.20  fof(c_0_21, plain, ![X49, X50]:k1_enumset1(X49,X49,X50)=k2_tarski(X49,X50), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 17.04/17.20  fof(c_0_22, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 17.04/17.20  fof(c_0_23, plain, ![X54, X55, X56, X57]:k3_enumset1(X54,X54,X55,X56,X57)=k2_enumset1(X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 17.04/17.20  cnf(c_0_24, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 17.04/17.20  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 17.04/17.20  cnf(c_0_26, negated_conjecture, (r2_hidden(esk8_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 17.04/17.20  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 17.04/17.20  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 17.04/17.20  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 17.04/17.20  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 17.04/17.20  fof(c_0_31, plain, ![X48]:k2_tarski(X48,X48)=k1_tarski(X48), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 17.04/17.20  fof(c_0_32, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 17.04/17.20  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 17.04/17.20  cnf(c_0_34, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 17.04/17.20  cnf(c_0_35, negated_conjecture, (r2_hidden(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 17.04/17.20  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 17.04/17.20  cnf(c_0_37, negated_conjecture, (k3_xboole_0(esk6_0,esk7_0)=k1_tarski(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 17.04/17.20  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 17.04/17.20  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 17.04/17.20  cnf(c_0_40, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_33])).
% 17.04/17.20  cnf(c_0_41, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(esk6_0,X1))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 17.04/17.20  cnf(c_0_42, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).
% 17.04/17.20  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))=k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_28]), c_0_29]), c_0_39]), c_0_30])).
% 17.04/17.20  cnf(c_0_44, negated_conjecture, (r2_hidden(esk8_0,X1)|~r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(esk6_0,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 17.04/17.20  cnf(c_0_45, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 17.04/17.20  fof(c_0_46, plain, ![X25, X26, X27]:k3_xboole_0(k3_xboole_0(X25,X26),X27)=k3_xboole_0(X25,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 17.04/17.20  fof(c_0_47, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 17.04/17.20  cnf(c_0_48, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 17.04/17.20  cnf(c_0_49, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 17.04/17.20  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 17.04/17.20  fof(c_0_51, plain, ![X22]:k3_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 17.04/17.20  fof(c_0_52, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 17.04/17.20  cnf(c_0_53, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(esk7_0,X1))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_48])).
% 17.04/17.20  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 17.04/17.20  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_39]), c_0_39])).
% 17.04/17.20  cnf(c_0_56, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 17.04/17.20  fof(c_0_57, plain, ![X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X34,X33)|X34=X32|X33!=k1_tarski(X32))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_tarski(X32)))&((~r2_hidden(esk3_2(X36,X37),X37)|esk3_2(X36,X37)!=X36|X37=k1_tarski(X36))&(r2_hidden(esk3_2(X36,X37),X37)|esk3_2(X36,X37)=X36|X37=k1_tarski(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 17.04/17.20  cnf(c_0_58, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 17.04/17.20  cnf(c_0_59, negated_conjecture, (r2_hidden(esk8_0,X1)|~r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(esk7_0,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_53])).
% 17.04/17.20  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1))))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 17.04/17.20  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_56, c_0_39])).
% 17.04/17.20  cnf(c_0_62, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 17.04/17.20  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_39])).
% 17.04/17.20  cnf(c_0_64, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1)))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 17.04/17.20  cnf(c_0_65, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_54, c_0_61])).
% 17.04/17.20  cnf(c_0_66, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(esk5_0,X1))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 17.04/17.20  cnf(c_0_67, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_38]), c_0_28]), c_0_29]), c_0_30])).
% 17.04/17.20  cnf(c_0_68, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 17.04/17.20  cnf(c_0_69, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))=esk5_0), inference(spm,[status(thm)],[c_0_63, c_0_19])).
% 17.04/17.20  cnf(c_0_70, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(X1,esk7_0)))|~r2_hidden(esk8_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 17.04/17.20  cnf(c_0_71, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))|r2_hidden(esk8_0,k4_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_66, c_0_55])).
% 17.04/17.20  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk8_0,k4_xboole_0(X1,esk7_0))), inference(spm,[status(thm)],[c_0_40, c_0_48])).
% 17.04/17.20  cnf(c_0_73, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_67])).
% 17.04/17.20  cnf(c_0_74, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 17.04/17.20  cnf(c_0_75, negated_conjecture, (r2_hidden(esk8_0,X1)|~r2_hidden(esk8_0,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1)))), inference(spm,[status(thm)],[c_0_40, c_0_68])).
% 17.04/17.20  cnf(c_0_76, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)))))), inference(spm,[status(thm)],[c_0_54, c_0_54])).
% 17.04/17.20  cnf(c_0_77, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)))))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 17.04/17.20  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1))))=k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_54, c_0_69])).
% 17.04/17.20  cnf(c_0_79, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 17.04/17.20  cnf(c_0_80, negated_conjecture, (X1=esk8_0|~r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_73, c_0_43])).
% 17.04/17.20  cnf(c_0_81, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_74])).
% 17.04/17.20  cnf(c_0_82, negated_conjecture, (k3_xboole_0(esk5_0,esk7_0)!=k1_tarski(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 17.04/17.20  cnf(c_0_83, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),k4_xboole_0(X1,k4_xboole_0(X1,X2))))|~r2_hidden(esk8_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1)))),X2))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_54]), c_0_54])).
% 17.04/17.20  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)),esk5_0)))))=k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 17.04/17.20  cnf(c_0_85, negated_conjecture, (~r2_hidden(esk8_0,k4_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))))), inference(spm,[status(thm)],[c_0_40, c_0_79])).
% 17.04/17.20  cnf(c_0_86, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 17.04/17.20  cnf(c_0_87, negated_conjecture, (esk2_3(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)))=esk8_0|k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1)=k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 17.04/17.20  cnf(c_0_88, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))!=k3_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_38]), c_0_28]), c_0_29]), c_0_39]), c_0_30])).
% 17.04/17.20  cnf(c_0_89, negated_conjecture, (~r2_hidden(esk8_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))))))))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_55]), c_0_65]), c_0_55]), c_0_65]), c_0_65]), c_0_54]), c_0_55]), c_0_60]), c_0_55]), c_0_78]), c_0_60]), c_0_55]), c_0_78]), c_0_55]), c_0_65]), c_0_65]), c_0_55]), c_0_65]), c_0_78]), c_0_85])).
% 17.04/17.20  cnf(c_0_90, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)),X1)=k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))|r2_hidden(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_45])])).
% 17.04/17.20  cnf(c_0_91, negated_conjecture, (k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))!=k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))), inference(rw,[status(thm)],[c_0_88, c_0_43])).
% 17.04/17.20  cnf(c_0_92, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_76]), c_0_54]), c_0_60]), c_0_61]), c_0_60]), c_0_55]), c_0_78]), c_0_60]), c_0_61]), c_0_60]), c_0_55]), c_0_78]), c_0_91]), ['proof']).
% 17.04/17.20  # SZS output end CNFRefutation
% 17.04/17.20  # Proof object total steps             : 93
% 17.04/17.20  # Proof object clause steps            : 64
% 17.04/17.20  # Proof object formula steps           : 29
% 17.04/17.20  # Proof object conjectures             : 36
% 17.04/17.20  # Proof object clause conjectures      : 33
% 17.04/17.20  # Proof object formula conjectures     : 3
% 17.04/17.20  # Proof object initial clauses used    : 20
% 17.04/17.20  # Proof object initial formulas used   : 14
% 17.04/17.20  # Proof object generating inferences   : 31
% 17.04/17.20  # Proof object simplifying inferences  : 69
% 17.04/17.20  # Training examples: 0 positive, 0 negative
% 17.04/17.20  # Parsed axioms                        : 15
% 17.04/17.20  # Removed by relevancy pruning/SinE    : 0
% 17.04/17.20  # Initial clauses                      : 35
% 17.04/17.20  # Removed in clause preprocessing      : 5
% 17.04/17.20  # Initial clauses in saturation        : 30
% 17.04/17.20  # Processed clauses                    : 23019
% 17.04/17.20  # ...of these trivial                  : 1554
% 17.04/17.20  # ...subsumed                          : 17218
% 17.04/17.20  # ...remaining for further processing  : 4247
% 17.04/17.20  # Other redundant clauses eliminated   : 227
% 17.04/17.20  # Clauses deleted for lack of memory   : 0
% 17.04/17.20  # Backward-subsumed                    : 85
% 17.04/17.20  # Backward-rewritten                   : 1518
% 17.04/17.20  # Generated clauses                    : 994713
% 17.04/17.20  # ...of the previous two non-trivial   : 843797
% 17.04/17.20  # Contextual simplify-reflections      : 3
% 17.04/17.20  # Paramodulations                      : 994186
% 17.04/17.20  # Factorizations                       : 303
% 17.04/17.20  # Equation resolutions                 : 227
% 17.04/17.20  # Propositional unsat checks           : 0
% 17.04/17.20  #    Propositional check models        : 0
% 17.04/17.20  #    Propositional check unsatisfiable : 0
% 17.04/17.20  #    Propositional clauses             : 0
% 17.04/17.20  #    Propositional clauses after purity: 0
% 17.04/17.20  #    Propositional unsat core size     : 0
% 17.04/17.20  #    Propositional preprocessing time  : 0.000
% 17.04/17.20  #    Propositional encoding time       : 0.000
% 17.04/17.20  #    Propositional solver time         : 0.000
% 17.04/17.20  #    Success case prop preproc time    : 0.000
% 17.04/17.20  #    Success case prop encoding time   : 0.000
% 17.04/17.20  #    Success case prop solver time     : 0.000
% 17.04/17.20  # Current number of processed clauses  : 2606
% 17.04/17.20  #    Positive orientable unit clauses  : 825
% 17.04/17.20  #    Positive unorientable unit clauses: 66
% 17.04/17.20  #    Negative unit clauses             : 673
% 17.04/17.20  #    Non-unit-clauses                  : 1042
% 17.04/17.20  # Current number of unprocessed clauses: 817799
% 17.04/17.20  # ...number of literals in the above   : 2080224
% 17.04/17.20  # Current number of archived formulas  : 0
% 17.04/17.20  # Current number of archived clauses   : 1636
% 17.04/17.20  # Clause-clause subsumption calls (NU) : 377681
% 17.04/17.20  # Rec. Clause-clause subsumption calls : 314726
% 17.04/17.20  # Non-unit clause-clause subsumptions  : 5728
% 17.04/17.20  # Unit Clause-clause subsumption calls : 515336
% 17.04/17.20  # Rewrite failures with RHS unbound    : 248
% 17.04/17.20  # BW rewrite match attempts            : 504286
% 17.04/17.20  # BW rewrite match successes           : 1769
% 17.04/17.20  # Condensation attempts                : 0
% 17.04/17.20  # Condensation successes               : 0
% 17.04/17.20  # Termbank termtop insertions          : 52829523
% 17.04/17.25  
% 17.04/17.25  # -------------------------------------------------
% 17.04/17.25  # User time                : 16.346 s
% 17.04/17.25  # System time              : 0.573 s
% 17.04/17.25  # Total time               : 16.919 s
% 17.04/17.25  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
