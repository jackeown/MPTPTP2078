%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:40 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.06s
% Verified   : 
% Statistics : Number of formulae       :   86 (1149 expanded)
%              Number of clauses        :   61 ( 473 expanded)
%              Number of leaves         :   12 ( 331 expanded)
%              Depth                    :   14
%              Number of atoms          :  173 (1603 expanded)
%              Number of equality atoms :   87 (1234 expanded)
%              Maximal formula depth    :   16 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t63_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X45,X46,X47] :
      ( k3_xboole_0(k2_tarski(X45,X46),X47) != k2_tarski(X45,X46)
      | r2_hidden(X45,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    & k3_xboole_0(esk5_0,esk6_0) = k1_tarski(esk7_0)
    & r2_hidden(esk7_0,esk4_0)
    & k3_xboole_0(esk4_0,esk6_0) != k1_tarski(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_18,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X25,X26,X27] : k3_xboole_0(k3_xboole_0(X25,X26),X27) = k3_xboole_0(X25,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | k3_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X22] : k3_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_28,plain,(
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

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X1,X1,X1,X2),X3)) != k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) = k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
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

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))) != k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_23])).

fof(c_0_37,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_25]),c_0_21]),c_0_22])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk6_0,X1))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_23]),c_0_23])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | ~ r2_hidden(esk7_0,k4_xboole_0(X2,k4_xboole_0(esk6_0,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_47])).

cnf(c_0_52,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_30])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r2_hidden(esk7_0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1))))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_25]),c_0_21]),c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))
    | ~ r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | ~ r2_hidden(esk7_0,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_59])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_31])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_47])).

cnf(c_0_71,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_30])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | ~ r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))),X2)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_31]),c_0_31])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)),esk4_0))))) = k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_47]),c_0_31])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_70])).

cnf(c_0_79,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( esk2_3(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))) = esk7_0
    | k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1) = k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) != k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_25]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))))))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_47]),c_0_76]),c_0_47]),c_0_76]),c_0_76]),c_0_31]),c_0_47]),c_0_77]),c_0_69]),c_0_77]),c_0_69]),c_0_47]),c_0_76]),c_0_76]),c_0_47]),c_0_76]),c_0_69]),c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1) = k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))
    | r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_53])])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) != k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_30])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_67]),c_0_31]),c_0_77]),c_0_36]),c_0_77]),c_0_69]),c_0_77]),c_0_36]),c_0_77]),c_0_69]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 12.06/12.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 12.06/12.29  # and selection function SelectCQArNTNpEqFirst.
% 12.06/12.29  #
% 12.06/12.29  # Preprocessing time       : 0.028 s
% 12.06/12.29  # Presaturation interreduction done
% 12.06/12.29  
% 12.06/12.29  # Proof found!
% 12.06/12.29  # SZS status Theorem
% 12.06/12.29  # SZS output start CNFRefutation
% 12.06/12.29  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 12.06/12.29  fof(t63_zfmisc_1, axiom, ![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 12.06/12.29  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.06/12.29  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 12.06/12.29  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.06/12.29  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.06/12.29  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 12.06/12.29  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 12.06/12.29  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.06/12.29  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 12.06/12.29  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.06/12.29  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.06/12.29  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 12.06/12.29  fof(c_0_13, plain, ![X45, X46, X47]:(k3_xboole_0(k2_tarski(X45,X46),X47)!=k2_tarski(X45,X46)|r2_hidden(X45,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_zfmisc_1])])).
% 12.06/12.29  fof(c_0_14, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 12.06/12.29  fof(c_0_15, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 12.06/12.29  fof(c_0_16, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 12.06/12.29  fof(c_0_17, negated_conjecture, (((r1_tarski(esk4_0,esk5_0)&k3_xboole_0(esk5_0,esk6_0)=k1_tarski(esk7_0))&r2_hidden(esk7_0,esk4_0))&k3_xboole_0(esk4_0,esk6_0)!=k1_tarski(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 12.06/12.29  fof(c_0_18, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 12.06/12.29  fof(c_0_19, plain, ![X25, X26, X27]:k3_xboole_0(k3_xboole_0(X25,X26),X27)=k3_xboole_0(X25,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 12.06/12.29  cnf(c_0_20, plain, (r2_hidden(X1,X3)|k3_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 12.06/12.29  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 12.06/12.29  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.06/12.29  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 12.06/12.29  cnf(c_0_24, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.06/12.29  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.06/12.29  cnf(c_0_26, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.06/12.29  fof(c_0_27, plain, ![X22]:k3_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 12.06/12.29  fof(c_0_28, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 12.06/12.29  cnf(c_0_29, plain, (r2_hidden(X1,X3)|k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X1,X1,X1,X2),X3))!=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23])).
% 12.06/12.29  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_21]), c_0_22]), c_0_23])).
% 12.06/12.29  cnf(c_0_31, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 12.06/12.29  cnf(c_0_32, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 12.06/12.29  fof(c_0_33, plain, ![X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X34,X33)|X34=X32|X33!=k1_tarski(X32))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_tarski(X32)))&((~r2_hidden(esk3_2(X36,X37),X37)|esk3_2(X36,X37)!=X36|X37=k1_tarski(X36))&(r2_hidden(esk3_2(X36,X37),X37)|esk3_2(X36,X37)=X36|X37=k1_tarski(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 12.06/12.29  cnf(c_0_34, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 12.06/12.29  cnf(c_0_35, negated_conjecture, (r2_hidden(esk7_0,X1)|k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1))))!=k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 12.06/12.29  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_32, c_0_23])).
% 12.06/12.29  fof(c_0_37, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 12.06/12.29  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 12.06/12.29  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 12.06/12.29  cnf(c_0_40, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_34])).
% 12.06/12.29  cnf(c_0_41, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 12.06/12.29  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 12.06/12.29  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_25]), c_0_21]), c_0_22])).
% 12.06/12.29  fof(c_0_44, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 12.06/12.29  cnf(c_0_45, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_39])).
% 12.06/12.29  cnf(c_0_46, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk6_0,X1))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 12.06/12.29  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_23]), c_0_23])).
% 12.06/12.29  cnf(c_0_48, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 12.06/12.29  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 12.06/12.29  cnf(c_0_50, negated_conjecture, (r2_hidden(esk7_0,X1)|~r2_hidden(esk7_0,k4_xboole_0(X2,k4_xboole_0(esk6_0,X1)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 12.06/12.29  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1))))), inference(spm,[status(thm)],[c_0_31, c_0_47])).
% 12.06/12.29  cnf(c_0_52, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 12.06/12.29  cnf(c_0_53, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_48, c_0_30])).
% 12.06/12.29  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_23])).
% 12.06/12.29  cnf(c_0_55, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.06/12.29  cnf(c_0_56, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~r2_hidden(esk7_0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 12.06/12.29  cnf(c_0_57, negated_conjecture, (r2_hidden(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.06/12.29  cnf(c_0_58, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_25]), c_0_21]), c_0_22])).
% 12.06/12.29  cnf(c_0_59, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_53])).
% 12.06/12.29  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))=esk4_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 12.06/12.29  cnf(c_0_61, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))|~r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_56, c_0_36])).
% 12.06/12.29  cnf(c_0_62, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk4_0,X1))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_57])).
% 12.06/12.29  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 12.06/12.29  cnf(c_0_64, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_58])).
% 12.06/12.29  cnf(c_0_65, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 12.06/12.29  cnf(c_0_66, negated_conjecture, (r2_hidden(esk7_0,X1)|~r2_hidden(esk7_0,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1)))), inference(spm,[status(thm)],[c_0_45, c_0_59])).
% 12.06/12.29  cnf(c_0_67, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)))))), inference(spm,[status(thm)],[c_0_31, c_0_31])).
% 12.06/12.29  cnf(c_0_68, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)))))), inference(spm,[status(thm)],[c_0_31, c_0_47])).
% 12.06/12.29  cnf(c_0_69, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_31, c_0_60])).
% 12.06/12.29  cnf(c_0_70, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_47])).
% 12.06/12.29  cnf(c_0_71, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_64, c_0_30])).
% 12.06/12.29  cnf(c_0_72, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_65])).
% 12.06/12.29  cnf(c_0_73, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.06/12.29  cnf(c_0_74, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),k4_xboole_0(X1,k4_xboole_0(X1,X2))))|~r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))),X2))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_31]), c_0_31])).
% 12.06/12.29  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)),esk4_0)))))=k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,X1)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 12.06/12.29  cnf(c_0_76, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 12.06/12.29  cnf(c_0_77, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_47]), c_0_31])).
% 12.06/12.29  cnf(c_0_78, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_45, c_0_70])).
% 12.06/12.29  cnf(c_0_79, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 12.06/12.29  cnf(c_0_80, negated_conjecture, (esk2_3(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)))=esk7_0|k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1)=k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 12.06/12.29  cnf(c_0_81, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))!=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_25]), c_0_21]), c_0_22]), c_0_23])).
% 12.06/12.29  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))))))))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_47]), c_0_76]), c_0_47]), c_0_76]), c_0_76]), c_0_31]), c_0_47]), c_0_77]), c_0_69]), c_0_77]), c_0_69]), c_0_47]), c_0_76]), c_0_76]), c_0_47]), c_0_76]), c_0_69]), c_0_78])).
% 12.06/12.29  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),X1)=k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))|r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_53])])).
% 12.06/12.29  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))!=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[c_0_81, c_0_30])).
% 12.06/12.29  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_67]), c_0_31]), c_0_77]), c_0_36]), c_0_77]), c_0_69]), c_0_77]), c_0_36]), c_0_77]), c_0_69]), c_0_84]), ['proof']).
% 12.06/12.29  # SZS output end CNFRefutation
% 12.06/12.29  # Proof object total steps             : 86
% 12.06/12.29  # Proof object clause steps            : 61
% 12.06/12.29  # Proof object formula steps           : 25
% 12.06/12.29  # Proof object conjectures             : 32
% 12.06/12.29  # Proof object clause conjectures      : 29
% 12.06/12.29  # Proof object formula conjectures     : 3
% 12.06/12.29  # Proof object initial clauses used    : 19
% 12.06/12.29  # Proof object initial formulas used   : 12
% 12.06/12.29  # Proof object generating inferences   : 28
% 12.06/12.29  # Proof object simplifying inferences  : 70
% 12.06/12.29  # Training examples: 0 positive, 0 negative
% 12.06/12.29  # Parsed axioms                        : 14
% 12.06/12.29  # Removed by relevancy pruning/SinE    : 0
% 12.06/12.29  # Initial clauses                      : 29
% 12.06/12.29  # Removed in clause preprocessing      : 4
% 12.06/12.29  # Initial clauses in saturation        : 25
% 12.06/12.29  # Processed clauses                    : 15176
% 12.06/12.29  # ...of these trivial                  : 1050
% 12.06/12.29  # ...subsumed                          : 10872
% 12.06/12.29  # ...remaining for further processing  : 3254
% 12.06/12.29  # Other redundant clauses eliminated   : 64
% 12.06/12.29  # Clauses deleted for lack of memory   : 0
% 12.06/12.29  # Backward-subsumed                    : 66
% 12.06/12.29  # Backward-rewritten                   : 362
% 12.06/12.29  # Generated clauses                    : 659583
% 12.06/12.29  # ...of the previous two non-trivial   : 578987
% 12.06/12.29  # Contextual simplify-reflections      : 3
% 12.06/12.29  # Paramodulations                      : 659401
% 12.06/12.29  # Factorizations                       : 118
% 12.06/12.29  # Equation resolutions                 : 64
% 12.06/12.29  # Propositional unsat checks           : 0
% 12.06/12.29  #    Propositional check models        : 0
% 12.06/12.29  #    Propositional check unsatisfiable : 0
% 12.06/12.29  #    Propositional clauses             : 0
% 12.06/12.29  #    Propositional clauses after purity: 0
% 12.06/12.29  #    Propositional unsat core size     : 0
% 12.06/12.29  #    Propositional preprocessing time  : 0.000
% 12.06/12.29  #    Propositional encoding time       : 0.000
% 12.06/12.29  #    Propositional solver time         : 0.000
% 12.06/12.29  #    Success case prop preproc time    : 0.000
% 12.06/12.29  #    Success case prop encoding time   : 0.000
% 12.06/12.29  #    Success case prop solver time     : 0.000
% 12.06/12.29  # Current number of processed clauses  : 2794
% 12.06/12.29  #    Positive orientable unit clauses  : 1092
% 12.06/12.29  #    Positive unorientable unit clauses: 66
% 12.06/12.29  #    Negative unit clauses             : 889
% 12.06/12.29  #    Non-unit-clauses                  : 747
% 12.06/12.29  # Current number of unprocessed clauses: 560715
% 12.06/12.29  # ...number of literals in the above   : 1147613
% 12.06/12.29  # Current number of archived formulas  : 0
% 12.06/12.29  # Current number of archived clauses   : 457
% 12.06/12.29  # Clause-clause subsumption calls (NU) : 124292
% 12.06/12.29  # Rec. Clause-clause subsumption calls : 112612
% 12.06/12.29  # Non-unit clause-clause subsumptions  : 3051
% 12.06/12.29  # Unit Clause-clause subsumption calls : 248158
% 12.06/12.29  # Rewrite failures with RHS unbound    : 216
% 12.06/12.29  # BW rewrite match attempts            : 371508
% 12.06/12.29  # BW rewrite match successes           : 1781
% 12.06/12.29  # Condensation attempts                : 0
% 12.06/12.29  # Condensation successes               : 0
% 12.06/12.29  # Termbank termtop insertions          : 41361102
% 12.14/12.33  
% 12.14/12.33  # -------------------------------------------------
% 12.14/12.33  # User time                : 11.580 s
% 12.14/12.33  # System time              : 0.403 s
% 12.14/12.33  # Total time               : 11.983 s
% 12.14/12.33  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
