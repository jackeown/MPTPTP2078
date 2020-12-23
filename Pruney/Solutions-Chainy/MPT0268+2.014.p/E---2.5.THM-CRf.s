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
% DateTime   : Thu Dec  3 10:42:19 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 456 expanded)
%              Number of clauses        :   41 ( 217 expanded)
%              Number of leaves         :   11 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 (1372 expanded)
%              Number of equality atoms :   96 ( 772 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X23)
        | X24 = k4_xboole_0(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X23)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X30] : k4_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_16,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40,X41,X42] :
      ( ( ~ r2_hidden(X37,X36)
        | X37 = X33
        | X37 = X34
        | X37 = X35
        | X36 != k1_enumset1(X33,X34,X35) )
      & ( X38 != X33
        | r2_hidden(X38,X36)
        | X36 != k1_enumset1(X33,X34,X35) )
      & ( X38 != X34
        | r2_hidden(X38,X36)
        | X36 != k1_enumset1(X33,X34,X35) )
      & ( X38 != X35
        | r2_hidden(X38,X36)
        | X36 != k1_enumset1(X33,X34,X35) )
      & ( esk4_4(X39,X40,X41,X42) != X39
        | ~ r2_hidden(esk4_4(X39,X40,X41,X42),X42)
        | X42 = k1_enumset1(X39,X40,X41) )
      & ( esk4_4(X39,X40,X41,X42) != X40
        | ~ r2_hidden(esk4_4(X39,X40,X41,X42),X42)
        | X42 = k1_enumset1(X39,X40,X41) )
      & ( esk4_4(X39,X40,X41,X42) != X41
        | ~ r2_hidden(esk4_4(X39,X40,X41,X42),X42)
        | X42 = k1_enumset1(X39,X40,X41) )
      & ( r2_hidden(esk4_4(X39,X40,X41,X42),X42)
        | esk4_4(X39,X40,X41,X42) = X39
        | esk4_4(X39,X40,X41,X42) = X40
        | esk4_4(X39,X40,X41,X42) = X41
        | X42 = k1_enumset1(X39,X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_17,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X50,X51,X52,X53] : k3_enumset1(X50,X50,X51,X52,X53) = k2_enumset1(X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

cnf(c_0_20,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,
    ( ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) != esk5_0
      | r2_hidden(esk6_0,esk5_0) )
    & ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) = esk5_0
      | ~ r2_hidden(esk6_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_26,plain,(
    ! [X44] : k2_tarski(X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X45,X46] : k1_enumset1(X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | k4_xboole_0(esk5_0,k1_tarski(esk6_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X26] :
      ( X26 = k1_xboole_0
      | r2_hidden(esk3_1(X26),X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_35,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_14]),c_0_23]),c_0_24])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))
    | r2_hidden(esk6_0,esk5_0)
    | k5_xboole_0(esk5_0,k1_xboole_0) != esk5_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,k1_xboole_0,X2),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_23]),c_0_24])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))
    | r2_hidden(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) = esk5_0
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk5_0)
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk6_0
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk5_0
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_32]),c_0_33]),c_0_14]),c_0_23]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_23]),c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_59])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.52  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.52  # and selection function SelectNegativeLiterals.
% 0.21/0.52  #
% 0.21/0.52  # Preprocessing time       : 0.028 s
% 0.21/0.52  # Presaturation interreduction done
% 0.21/0.52  
% 0.21/0.52  # Proof found!
% 0.21/0.52  # SZS status Theorem
% 0.21/0.52  # SZS output start CNFRefutation
% 0.21/0.52  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.21/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.52  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.52  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.21/0.52  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.52  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.52  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.21/0.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.52  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.52  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.52  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.21/0.52  fof(c_0_11, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:((((r2_hidden(X20,X17)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18)))&(~r2_hidden(X21,X17)|r2_hidden(X21,X18)|r2_hidden(X21,X19)|X19!=k4_xboole_0(X17,X18)))&((~r2_hidden(esk2_3(X22,X23,X24),X24)|(~r2_hidden(esk2_3(X22,X23,X24),X22)|r2_hidden(esk2_3(X22,X23,X24),X23))|X24=k4_xboole_0(X22,X23))&((r2_hidden(esk2_3(X22,X23,X24),X22)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))&(~r2_hidden(esk2_3(X22,X23,X24),X23)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.21/0.52  fof(c_0_12, plain, ![X28, X29]:k4_xboole_0(X28,X29)=k5_xboole_0(X28,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.52  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.52  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.52  fof(c_0_15, plain, ![X30]:k4_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.52  fof(c_0_16, plain, ![X33, X34, X35, X36, X37, X38, X39, X40, X41, X42]:(((~r2_hidden(X37,X36)|(X37=X33|X37=X34|X37=X35)|X36!=k1_enumset1(X33,X34,X35))&(((X38!=X33|r2_hidden(X38,X36)|X36!=k1_enumset1(X33,X34,X35))&(X38!=X34|r2_hidden(X38,X36)|X36!=k1_enumset1(X33,X34,X35)))&(X38!=X35|r2_hidden(X38,X36)|X36!=k1_enumset1(X33,X34,X35))))&((((esk4_4(X39,X40,X41,X42)!=X39|~r2_hidden(esk4_4(X39,X40,X41,X42),X42)|X42=k1_enumset1(X39,X40,X41))&(esk4_4(X39,X40,X41,X42)!=X40|~r2_hidden(esk4_4(X39,X40,X41,X42),X42)|X42=k1_enumset1(X39,X40,X41)))&(esk4_4(X39,X40,X41,X42)!=X41|~r2_hidden(esk4_4(X39,X40,X41,X42),X42)|X42=k1_enumset1(X39,X40,X41)))&(r2_hidden(esk4_4(X39,X40,X41,X42),X42)|(esk4_4(X39,X40,X41,X42)=X39|esk4_4(X39,X40,X41,X42)=X40|esk4_4(X39,X40,X41,X42)=X41)|X42=k1_enumset1(X39,X40,X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.21/0.52  fof(c_0_17, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.52  fof(c_0_18, plain, ![X50, X51, X52, X53]:k3_enumset1(X50,X50,X51,X52,X53)=k2_enumset1(X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.52  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.21/0.52  cnf(c_0_20, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.52  cnf(c_0_21, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.52  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.52  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  fof(c_0_25, negated_conjecture, ((k4_xboole_0(esk5_0,k1_tarski(esk6_0))!=esk5_0|r2_hidden(esk6_0,esk5_0))&(k4_xboole_0(esk5_0,k1_tarski(esk6_0))=esk5_0|~r2_hidden(esk6_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.21/0.52  fof(c_0_26, plain, ![X44]:k2_tarski(X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.52  fof(c_0_27, plain, ![X45, X46]:k1_enumset1(X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.52  cnf(c_0_28, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_20])).
% 0.21/0.52  cnf(c_0_29, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_21, c_0_14])).
% 0.21/0.52  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.21/0.52  cnf(c_0_31, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|k4_xboole_0(esk5_0,k1_tarski(esk6_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.52  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.52  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.52  fof(c_0_34, plain, ![X26]:(X26=k1_xboole_0|r2_hidden(esk3_1(X26),X26)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.52  fof(c_0_35, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.21/0.52  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.52  cnf(c_0_37, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 0.21/0.52  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_14]), c_0_23]), c_0_24])).
% 0.21/0.52  cnf(c_0_39, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.52  cnf(c_0_40, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.52  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.52  cnf(c_0_42, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.52  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.52  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))|r2_hidden(esk6_0,esk5_0)|k5_xboole_0(esk5_0,k1_xboole_0)!=esk5_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.52  cnf(c_0_45, plain, (k5_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,k1_xboole_0,X2),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_41])).
% 0.21/0.52  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.52  cnf(c_0_47, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_23]), c_0_24])).
% 0.21/0.52  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_43])).
% 0.21/0.52  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))|r2_hidden(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_41])).
% 0.21/0.52  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_46])).
% 0.21/0.52  cnf(c_0_51, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_47])).
% 0.21/0.52  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.52  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk5_0,k1_tarski(esk6_0))=esk5_0|~r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.52  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk5_0)|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.21/0.52  cnf(c_0_55, negated_conjecture, (esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk6_0|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.52  cnf(c_0_56, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk5_0|~r2_hidden(esk6_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_32]), c_0_33]), c_0_14]), c_0_23]), c_0_24])).
% 0.21/0.52  cnf(c_0_57, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.52  cnf(c_0_58, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.52  cnf(c_0_59, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.21/0.52  cnf(c_0_60, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_23]), c_0_24])).
% 0.21/0.52  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_59])).
% 0.21/0.52  cnf(c_0_62, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).
% 0.21/0.52  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_57])]), ['proof']).
% 0.21/0.52  # SZS output end CNFRefutation
% 0.21/0.52  # Proof object total steps             : 64
% 0.21/0.52  # Proof object clause steps            : 41
% 0.21/0.52  # Proof object formula steps           : 23
% 0.21/0.52  # Proof object conjectures             : 16
% 0.21/0.52  # Proof object clause conjectures      : 13
% 0.21/0.52  # Proof object formula conjectures     : 3
% 0.21/0.52  # Proof object initial clauses used    : 16
% 0.21/0.52  # Proof object initial formulas used   : 11
% 0.21/0.52  # Proof object generating inferences   : 11
% 0.21/0.52  # Proof object simplifying inferences  : 32
% 0.21/0.52  # Training examples: 0 positive, 0 negative
% 0.21/0.52  # Parsed axioms                        : 14
% 0.21/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.52  # Initial clauses                      : 33
% 0.21/0.52  # Removed in clause preprocessing      : 5
% 0.21/0.52  # Initial clauses in saturation        : 28
% 0.21/0.52  # Processed clauses                    : 621
% 0.21/0.52  # ...of these trivial                  : 86
% 0.21/0.52  # ...subsumed                          : 281
% 0.21/0.52  # ...remaining for further processing  : 254
% 0.21/0.52  # Other redundant clauses eliminated   : 114
% 0.21/0.52  # Clauses deleted for lack of memory   : 0
% 0.21/0.52  # Backward-subsumed                    : 2
% 0.21/0.52  # Backward-rewritten                   : 15
% 0.21/0.52  # Generated clauses                    : 16755
% 0.21/0.52  # ...of the previous two non-trivial   : 10370
% 0.21/0.52  # Contextual simplify-reflections      : 0
% 0.21/0.52  # Paramodulations                      : 16638
% 0.21/0.52  # Factorizations                       : 6
% 0.21/0.52  # Equation resolutions                 : 114
% 0.21/0.52  # Propositional unsat checks           : 0
% 0.21/0.52  #    Propositional check models        : 0
% 0.21/0.52  #    Propositional check unsatisfiable : 0
% 0.21/0.52  #    Propositional clauses             : 0
% 0.21/0.52  #    Propositional clauses after purity: 0
% 0.21/0.52  #    Propositional unsat core size     : 0
% 0.21/0.52  #    Propositional preprocessing time  : 0.000
% 0.21/0.52  #    Propositional encoding time       : 0.000
% 0.21/0.52  #    Propositional solver time         : 0.000
% 0.21/0.52  #    Success case prop preproc time    : 0.000
% 0.21/0.52  #    Success case prop encoding time   : 0.000
% 0.21/0.52  #    Success case prop solver time     : 0.000
% 0.21/0.52  # Current number of processed clauses  : 199
% 0.21/0.52  #    Positive orientable unit clauses  : 89
% 0.21/0.52  #    Positive unorientable unit clauses: 1
% 0.21/0.52  #    Negative unit clauses             : 1
% 0.21/0.52  #    Non-unit-clauses                  : 108
% 0.21/0.52  # Current number of unprocessed clauses: 9727
% 0.21/0.52  # ...number of literals in the above   : 26067
% 0.21/0.52  # Current number of archived formulas  : 0
% 0.21/0.52  # Current number of archived clauses   : 50
% 0.21/0.52  # Clause-clause subsumption calls (NU) : 3145
% 0.21/0.52  # Rec. Clause-clause subsumption calls : 2744
% 0.21/0.52  # Non-unit clause-clause subsumptions  : 174
% 0.21/0.52  # Unit Clause-clause subsumption calls : 140
% 0.21/0.52  # Rewrite failures with RHS unbound    : 0
% 0.21/0.52  # BW rewrite match attempts            : 582
% 0.21/0.52  # BW rewrite match successes           : 15
% 0.21/0.52  # Condensation attempts                : 0
% 0.21/0.52  # Condensation successes               : 0
% 0.21/0.52  # Termbank termtop insertions          : 271023
% 0.21/0.52  
% 0.21/0.52  # -------------------------------------------------
% 0.21/0.52  # User time                : 0.164 s
% 0.21/0.52  # System time              : 0.008 s
% 0.21/0.52  # Total time               : 0.172 s
% 0.21/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
