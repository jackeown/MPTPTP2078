%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 (9507 expanded)
%              Number of clauses        :   61 (4031 expanded)
%              Number of leaves         :   12 (2642 expanded)
%              Depth                    :   19
%              Number of atoms          :  205 (18494 expanded)
%              Number of equality atoms :  103 (13386 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t44_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_12,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X26
        | X27 != k1_tarski(X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_tarski(X26) )
      & ( ~ r2_hidden(esk4_2(X30,X31),X31)
        | esk4_2(X30,X31) != X30
        | X31 = k1_tarski(X30) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | esk4_2(X30,X31) = X30
        | X31 = k1_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_19,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & esk6_0 != esk7_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_21]),c_0_29]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_22]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_36,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk3_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( esk5_0 = esk3_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_41,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( X1 = esk3_1(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_43,plain,
    ( esk4_2(X1,X2) = X1
    | X2 = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(esk4_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_44,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk4_2(X1,esk6_0) = esk3_1(esk6_0)
    | esk4_2(X1,esk6_0) = X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_46,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_47,plain,
    ( X2 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk4_2(X1,X2) != X1
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)) = esk6_0
    | esk4_2(esk3_1(esk6_0),esk6_0) = esk3_1(esk6_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_45])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_50,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_51,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)) = esk6_0
    | ~ r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_29]),c_0_22]),c_0_23])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_29]),c_0_22]),c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_38]),c_0_39])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_29]),c_0_22]),c_0_23])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) = k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X2,X1),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_1(esk6_0),k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( esk3_1(esk6_0) = k3_tarski(esk6_0)
    | ~ r2_hidden(esk1_2(k3_tarski(esk6_0),esk3_1(esk6_0)),esk3_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,esk3_1(esk6_0))
    | ~ r2_hidden(X1,k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( esk3_1(esk6_0) = k3_tarski(esk6_0)
    | r2_hidden(esk1_2(k3_tarski(esk6_0),esk3_1(esk6_0)),k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_74,negated_conjecture,
    ( esk3_1(esk6_0) = k3_tarski(esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_38]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( X1 = k3_tarski(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( esk7_0 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk4_2(X1,esk7_0) = X1
    | r2_hidden(esk4_2(X1,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( esk3_1(esk7_0) = esk3_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk4_2(X1,esk7_0) = k3_tarski(esk6_0)
    | esk4_2(X1,esk7_0) = X1 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k3_enumset1(k3_tarski(esk6_0),k3_tarski(esk6_0),k3_tarski(esk6_0),k3_tarski(esk6_0),k3_tarski(esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_74]),c_0_74]),c_0_74]),c_0_74]),c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_78]),c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( esk4_2(k3_tarski(esk6_0),esk7_0) = k3_tarski(esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_79])]),c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k3_tarski(esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_83]),c_0_80]),c_0_84])]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.38  fof(t44_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.19/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(c_0_12, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|X28=X26|X27!=k1_tarski(X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_tarski(X26)))&((~r2_hidden(esk4_2(X30,X31),X31)|esk4_2(X30,X31)!=X30|X31=k1_tarski(X30))&(r2_hidden(esk4_2(X30,X31),X31)|esk4_2(X30,X31)=X30|X31=k1_tarski(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_14, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_15, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_16, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t44_zfmisc_1])).
% 0.19/0.38  fof(c_0_18, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.38  cnf(c_0_19, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_24, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&esk6_0!=esk7_0)&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.19/0.38  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_26, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.38  cnf(c_0_27, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_21])).
% 0.19/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_31, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_21]), c_0_29]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.19/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.38  cnf(c_0_35, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.38  fof(c_0_36, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk3_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.38  cnf(c_0_38, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (esk5_0=esk3_1(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.38  cnf(c_0_41, plain, (r2_hidden(esk4_2(X1,X2),X2)|esk4_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (X1=esk3_1(esk6_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_37, c_0_40])).
% 0.19/0.38  cnf(c_0_43, plain, (esk4_2(X1,X2)=X1|X2=k3_enumset1(X1,X1,X1,X1,X1)|r2_hidden(esk4_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_44, plain, (X2=k1_tarski(X1)|~r2_hidden(esk4_2(X1,X2),X2)|esk4_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (esk6_0=k3_enumset1(X1,X1,X1,X1,X1)|esk4_2(X1,esk6_0)=esk3_1(esk6_0)|esk4_2(X1,esk6_0)=X1), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  fof(c_0_46, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.38  cnf(c_0_47, plain, (X2=k3_enumset1(X1,X1,X1,X1,X1)|esk4_2(X1,X2)!=X1|~r2_hidden(esk4_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))=esk6_0|esk4_2(esk3_1(esk6_0),esk6_0)=esk3_1(esk6_0)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_45])])).
% 0.19/0.38  cnf(c_0_49, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  fof(c_0_50, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_51, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))=esk6_0|~r2_hidden(esk3_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.38  cnf(c_0_54, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_29]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.38  cnf(c_0_58, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_29]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_38]), c_0_39])).
% 0.19/0.38  cnf(c_0_60, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_29]), c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_61, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.38  cnf(c_0_62, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))=k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.19/0.38  cnf(c_0_64, plain, (X1=X2|~r2_hidden(esk1_2(X2,X1),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_1(esk6_0),k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.38  cnf(c_0_66, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.38  cnf(c_0_67, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_61])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (esk3_1(esk6_0)=k3_tarski(esk6_0)|~r2_hidden(esk1_2(k3_tarski(esk6_0),esk3_1(esk6_0)),esk3_1(esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,esk3_1(esk6_0))|~r2_hidden(X1,k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_66, c_0_59])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (esk3_1(esk6_0)=k3_tarski(esk6_0)|r2_hidden(esk1_2(k3_tarski(esk6_0),esk3_1(esk6_0)),k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_67, c_0_65])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_68, c_0_59])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (esk3_1(esk6_0)=k3_tarski(esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (r2_hidden(esk3_1(esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_38]), c_0_73])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (X1=k3_tarski(esk6_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_42, c_0_74])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (esk7_0=k3_enumset1(X1,X1,X1,X1,X1)|esk4_2(X1,esk7_0)=X1|r2_hidden(esk4_2(X1,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_72, c_0_43])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (esk3_1(esk7_0)=esk3_1(esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_75])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (esk7_0=k3_enumset1(X1,X1,X1,X1,X1)|esk4_2(X1,esk7_0)=k3_tarski(esk6_0)|esk4_2(X1,esk7_0)=X1), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (k3_enumset1(k3_tarski(esk6_0),k3_tarski(esk6_0),k3_tarski(esk6_0),k3_tarski(esk6_0),k3_tarski(esk6_0))=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_74]), c_0_74]), c_0_74]), c_0_74]), c_0_74])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (esk6_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_78]), c_0_73])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (esk4_2(k3_tarski(esk6_0),esk7_0)=k3_tarski(esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_79])]), c_0_80]), c_0_81])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (r2_hidden(k3_tarski(esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_82, c_0_74])).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_83]), c_0_80]), c_0_84])]), c_0_81]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 86
% 0.19/0.38  # Proof object clause steps            : 61
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 34
% 0.19/0.38  # Proof object clause conjectures      : 31
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 20
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 22
% 0.19/0.38  # Proof object simplifying inferences  : 63
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 27
% 0.19/0.38  # Removed in clause preprocessing      : 5
% 0.19/0.38  # Initial clauses in saturation        : 22
% 0.19/0.38  # Processed clauses                    : 174
% 0.19/0.38  # ...of these trivial                  : 5
% 0.19/0.38  # ...subsumed                          : 35
% 0.19/0.38  # ...remaining for further processing  : 134
% 0.19/0.38  # Other redundant clauses eliminated   : 20
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 42
% 0.19/0.38  # Generated clauses                    : 488
% 0.19/0.38  # ...of the previous two non-trivial   : 412
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 448
% 0.19/0.38  # Factorizations                       : 21
% 0.19/0.38  # Equation resolutions                 : 20
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 63
% 0.19/0.38  #    Positive orientable unit clauses  : 11
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 49
% 0.19/0.38  # Current number of unprocessed clauses: 264
% 0.19/0.38  # ...number of literals in the above   : 907
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 69
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 470
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 359
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 36
% 0.19/0.38  # Unit Clause-clause subsumption calls : 17
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 10
% 0.19/0.38  # BW rewrite match successes           : 6
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8755
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.043 s
% 0.19/0.38  # System time              : 0.002 s
% 0.19/0.38  # Total time               : 0.045 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
