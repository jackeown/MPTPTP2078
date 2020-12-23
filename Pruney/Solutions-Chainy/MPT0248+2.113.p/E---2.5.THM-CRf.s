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
% DateTime   : Thu Dec  3 10:39:54 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   93 (3973 expanded)
%              Number of clauses        :   66 (1607 expanded)
%              Number of leaves         :   13 (1144 expanded)
%              Depth                    :   23
%              Number of atoms          :  223 (6580 expanded)
%              Number of equality atoms :  117 (5441 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_13,plain,(
    ! [X49,X50] : k3_tarski(k2_tarski(X49,X50)) = k2_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k2_xboole_0(X26,X27) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X43,X44,X45,X46] : k3_enumset1(X43,X43,X44,X45,X46) = k2_enumset1(X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X28,X29] : r1_tarski(X28,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_22,negated_conjecture,
    ( k1_tarski(esk6_0) = k2_xboole_0(esk7_0,esk8_0)
    & ( esk7_0 != k1_tarski(esk6_0)
      | esk8_0 != k1_tarski(esk6_0) )
    & ( esk7_0 != k1_xboole_0
      | esk8_0 != k1_tarski(esk6_0) )
    & ( esk7_0 != k1_tarski(esk6_0)
      | esk8_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_23,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_29,plain,(
    ! [X47,X48] :
      ( ( ~ r1_tarski(X47,k1_tarski(X48))
        | X47 = k1_xboole_0
        | X47 = k1_tarski(X48) )
      & ( X47 != k1_xboole_0
        | r1_tarski(X47,k1_tarski(X48)) )
      & ( X47 != k1_tarski(X48)
        | r1_tarski(X47,k1_tarski(X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k1_tarski(esk6_0) = k2_xboole_0(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_18]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk8_0 != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk7_0 != k1_tarski(esk6_0)
    | esk8_0 != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( esk7_0 != k1_tarski(esk6_0)
    | esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_32]),c_0_32]),c_0_18]),c_0_18]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk7_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X30
        | X31 != k1_tarski(X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_tarski(X30) )
      & ( ~ r2_hidden(esk5_2(X34,X35),X35)
        | esk5_2(X34,X35) != X34
        | X35 = k1_tarski(X34) )
      & ( r2_hidden(esk5_2(X34,X35),X35)
        | esk5_2(X34,X35) = X34
        | X35 = k1_tarski(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk8_0 != k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_32]),c_0_18]),c_0_26]),c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = esk8_0
    | r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 != k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | esk8_0 != k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_32]),c_0_32]),c_0_18]),c_0_18]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

fof(c_0_48,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X17)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X22)
        | r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k2_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_49,plain,(
    ! [X24] :
      ( X24 = k1_xboole_0
      | r2_hidden(esk4_1(X24),X24) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_50,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | esk7_0 != k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_32]),c_0_18]),c_0_26]),c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = esk7_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0)
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0)
    | esk8_0 != esk7_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_32]),c_0_18]),c_0_26]),c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_54]),c_0_55])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k1_xboole_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk4_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk4_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_2(esk7_0,esk8_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk4_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_32]),c_0_18]),c_0_26]),c_0_27])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( esk2_2(esk7_0,esk8_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_0),esk8_0)
    | r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0)
    | ~ r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_0),esk8_0)
    | r2_hidden(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk7_0,k1_xboole_0)
    | r2_hidden(esk4_1(esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_57]),c_0_76])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k1_xboole_0)) = k1_xboole_0
    | r2_hidden(esk4_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_77])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k1_xboole_0
    | r2_hidden(esk4_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_79])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_81]),c_0_64]),c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_0),k3_tarski(k3_enumset1(X1,X1,X1,X1,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_1(esk8_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_37])).

cnf(c_0_86,negated_conjecture,
    ( esk4_1(esk8_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_87])])).

cnf(c_0_89,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_88]),c_0_37])).

cnf(c_0_90,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 != esk7_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_51])).

cnf(c_0_91,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_89]),c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_89])]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.66  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.48/0.66  # and selection function SelectNegativeLiterals.
% 0.48/0.66  #
% 0.48/0.66  # Preprocessing time       : 0.028 s
% 0.48/0.66  # Presaturation interreduction done
% 0.48/0.66  
% 0.48/0.66  # Proof found!
% 0.48/0.66  # SZS status Theorem
% 0.48/0.66  # SZS output start CNFRefutation
% 0.48/0.66  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.48/0.66  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.66  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.48/0.66  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.48/0.66  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.66  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.66  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.48/0.66  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.48/0.66  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.48/0.66  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.48/0.66  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.48/0.66  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.48/0.66  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.48/0.66  fof(c_0_13, plain, ![X49, X50]:k3_tarski(k2_tarski(X49,X50))=k2_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.48/0.66  fof(c_0_14, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.66  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.48/0.66  fof(c_0_16, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k2_xboole_0(X26,X27)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.48/0.66  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.66  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.66  fof(c_0_19, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.66  fof(c_0_20, plain, ![X43, X44, X45, X46]:k3_enumset1(X43,X43,X44,X45,X46)=k2_enumset1(X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.66  fof(c_0_21, plain, ![X28, X29]:r1_tarski(X28,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.48/0.66  fof(c_0_22, negated_conjecture, (((k1_tarski(esk6_0)=k2_xboole_0(esk7_0,esk8_0)&(esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_tarski(esk6_0)))&(esk7_0!=k1_xboole_0|esk8_0!=k1_tarski(esk6_0)))&(esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.48/0.66  fof(c_0_23, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.48/0.66  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.66  cnf(c_0_25, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.48/0.66  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.66  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.66  fof(c_0_28, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.48/0.66  fof(c_0_29, plain, ![X47, X48]:((~r1_tarski(X47,k1_tarski(X48))|(X47=k1_xboole_0|X47=k1_tarski(X48)))&((X47!=k1_xboole_0|r1_tarski(X47,k1_tarski(X48)))&(X47!=k1_tarski(X48)|r1_tarski(X47,k1_tarski(X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.48/0.66  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.66  cnf(c_0_31, negated_conjecture, (k1_tarski(esk6_0)=k2_xboole_0(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.66  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.66  cnf(c_0_33, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_34, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.66  cnf(c_0_35, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.66  cnf(c_0_36, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_37, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_18]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.48/0.66  cnf(c_0_38, negated_conjecture, (esk7_0!=k1_xboole_0|esk8_0!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.66  cnf(c_0_39, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.48/0.66  cnf(c_0_40, negated_conjecture, (esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.66  cnf(c_0_41, negated_conjecture, (esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.66  cnf(c_0_42, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_32]), c_0_32]), c_0_18]), c_0_18]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.48/0.66  cnf(c_0_43, negated_conjecture, (r1_tarski(esk7_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.48/0.66  fof(c_0_44, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|X32=X30|X31!=k1_tarski(X30))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_tarski(X30)))&((~r2_hidden(esk5_2(X34,X35),X35)|esk5_2(X34,X35)!=X34|X35=k1_tarski(X34))&(r2_hidden(esk5_2(X34,X35),X35)|esk5_2(X34,X35)=X34|X35=k1_tarski(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.48/0.66  cnf(c_0_45, negated_conjecture, (esk7_0!=k1_xboole_0|esk8_0!=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_32]), c_0_18]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_46, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=esk8_0|r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_39])).
% 0.48/0.66  cnf(c_0_47, negated_conjecture, (esk7_0!=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|esk8_0!=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_32]), c_0_32]), c_0_18]), c_0_18]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.48/0.66  fof(c_0_48, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X18,X17)|(r2_hidden(X18,X15)|r2_hidden(X18,X16))|X17!=k2_xboole_0(X15,X16))&((~r2_hidden(X19,X15)|r2_hidden(X19,X17)|X17!=k2_xboole_0(X15,X16))&(~r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k2_xboole_0(X15,X16))))&(((~r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_xboole_0(X20,X21))&(~r2_hidden(esk3_3(X20,X21,X22),X21)|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_xboole_0(X20,X21)))&(r2_hidden(esk3_3(X20,X21,X22),X22)|(r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k2_xboole_0(X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.48/0.66  fof(c_0_49, plain, ![X24]:(X24=k1_xboole_0|r2_hidden(esk4_1(X24),X24)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.48/0.66  cnf(c_0_50, negated_conjecture, (esk8_0!=k1_xboole_0|esk7_0!=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_32]), c_0_18]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_51, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=esk7_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.48/0.66  cnf(c_0_52, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.48/0.66  cnf(c_0_53, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.66  cnf(c_0_54, negated_conjecture, (r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0)|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.48/0.66  cnf(c_0_55, negated_conjecture, (r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0)|esk8_0!=esk7_0), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.48/0.66  cnf(c_0_56, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.66  cnf(c_0_57, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.48/0.66  cnf(c_0_58, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.48/0.66  cnf(c_0_59, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_32]), c_0_18]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_53, c_0_43])).
% 0.48/0.66  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_2(esk7_0,esk8_0),esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_46]), c_0_54]), c_0_55])).
% 0.48/0.66  cnf(c_0_62, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_25]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_63, negated_conjecture, (k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k1_xboole_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk4_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_57])).
% 0.48/0.66  cnf(c_0_64, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk4_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 0.48/0.66  cnf(c_0_65, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.48/0.66  cnf(c_0_66, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.48/0.66  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_2(esk7_0,esk8_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.48/0.66  cnf(c_0_68, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_62])).
% 0.48/0.66  cnf(c_0_69, negated_conjecture, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk4_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.48/0.66  cnf(c_0_70, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_32]), c_0_18]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.66  cnf(c_0_72, negated_conjecture, (esk2_2(esk7_0,esk8_0)=esk6_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.48/0.66  cnf(c_0_73, negated_conjecture, (r2_hidden(esk4_1(esk8_0),esk8_0)|r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.48/0.66  cnf(c_0_74, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).
% 0.48/0.66  cnf(c_0_75, negated_conjecture, (r1_tarski(esk7_0,esk8_0)|~r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.48/0.66  cnf(c_0_76, negated_conjecture, (r2_hidden(esk4_1(esk8_0),esk8_0)|r2_hidden(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.48/0.66  cnf(c_0_77, negated_conjecture, (r1_tarski(esk7_0,k1_xboole_0)|r2_hidden(esk4_1(esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_57]), c_0_76])).
% 0.48/0.66  cnf(c_0_78, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.66  cnf(c_0_79, negated_conjecture, (k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k1_xboole_0))=k1_xboole_0|r2_hidden(esk4_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_77])).
% 0.48/0.66  cnf(c_0_80, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_25]), c_0_26]), c_0_27])).
% 0.48/0.66  cnf(c_0_81, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k1_xboole_0|r2_hidden(esk4_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_63, c_0_79])).
% 0.48/0.66  cnf(c_0_82, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_80])).
% 0.48/0.66  cnf(c_0_83, negated_conjecture, (r2_hidden(esk4_1(esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_81]), c_0_64]), c_0_57])).
% 0.48/0.66  cnf(c_0_84, negated_conjecture, (r2_hidden(esk4_1(esk8_0),k3_tarski(k3_enumset1(X1,X1,X1,X1,esk8_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.48/0.66  cnf(c_0_85, negated_conjecture, (r2_hidden(esk4_1(esk8_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_84, c_0_37])).
% 0.48/0.66  cnf(c_0_86, negated_conjecture, (esk4_1(esk8_0)=esk6_0), inference(spm,[status(thm)],[c_0_66, c_0_85])).
% 0.48/0.66  cnf(c_0_87, negated_conjecture, (r2_hidden(esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_83, c_0_86])).
% 0.48/0.66  cnf(c_0_88, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_87])])).
% 0.48/0.66  cnf(c_0_89, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_88]), c_0_37])).
% 0.48/0.66  cnf(c_0_90, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0!=esk7_0), inference(spm,[status(thm)],[c_0_47, c_0_51])).
% 0.48/0.66  cnf(c_0_91, negated_conjecture, (esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_89]), c_0_90])).
% 0.48/0.66  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_89])]), c_0_91])]), ['proof']).
% 0.48/0.66  # SZS output end CNFRefutation
% 0.48/0.66  # Proof object total steps             : 93
% 0.48/0.66  # Proof object clause steps            : 66
% 0.48/0.66  # Proof object formula steps           : 27
% 0.48/0.66  # Proof object conjectures             : 40
% 0.48/0.66  # Proof object clause conjectures      : 37
% 0.48/0.66  # Proof object formula conjectures     : 3
% 0.48/0.66  # Proof object initial clauses used    : 20
% 0.48/0.66  # Proof object initial formulas used   : 13
% 0.48/0.66  # Proof object generating inferences   : 27
% 0.48/0.66  # Proof object simplifying inferences  : 71
% 0.48/0.66  # Training examples: 0 positive, 0 negative
% 0.48/0.66  # Parsed axioms                        : 14
% 0.48/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.66  # Initial clauses                      : 30
% 0.48/0.66  # Removed in clause preprocessing      : 5
% 0.48/0.66  # Initial clauses in saturation        : 25
% 0.48/0.66  # Processed clauses                    : 1241
% 0.48/0.66  # ...of these trivial                  : 12
% 0.48/0.66  # ...subsumed                          : 704
% 0.48/0.66  # ...remaining for further processing  : 524
% 0.48/0.66  # Other redundant clauses eliminated   : 558
% 0.48/0.66  # Clauses deleted for lack of memory   : 0
% 0.48/0.66  # Backward-subsumed                    : 48
% 0.48/0.66  # Backward-rewritten                   : 365
% 0.48/0.66  # Generated clauses                    : 26724
% 0.48/0.66  # ...of the previous two non-trivial   : 22531
% 0.48/0.66  # Contextual simplify-reflections      : 19
% 0.48/0.66  # Paramodulations                      : 26116
% 0.48/0.66  # Factorizations                       : 51
% 0.48/0.66  # Equation resolutions                 : 558
% 0.48/0.66  # Propositional unsat checks           : 0
% 0.48/0.66  #    Propositional check models        : 0
% 0.48/0.66  #    Propositional check unsatisfiable : 0
% 0.48/0.66  #    Propositional clauses             : 0
% 0.48/0.66  #    Propositional clauses after purity: 0
% 0.48/0.66  #    Propositional unsat core size     : 0
% 0.48/0.66  #    Propositional preprocessing time  : 0.000
% 0.48/0.66  #    Propositional encoding time       : 0.000
% 0.48/0.66  #    Propositional solver time         : 0.000
% 0.48/0.66  #    Success case prop preproc time    : 0.000
% 0.48/0.66  #    Success case prop encoding time   : 0.000
% 0.48/0.66  #    Success case prop solver time     : 0.000
% 0.48/0.66  # Current number of processed clauses  : 79
% 0.48/0.66  #    Positive orientable unit clauses  : 17
% 0.48/0.66  #    Positive unorientable unit clauses: 0
% 0.48/0.66  #    Negative unit clauses             : 1
% 0.48/0.66  #    Non-unit-clauses                  : 61
% 0.48/0.66  # Current number of unprocessed clauses: 21077
% 0.48/0.66  # ...number of literals in the above   : 102450
% 0.48/0.66  # Current number of archived formulas  : 0
% 0.48/0.66  # Current number of archived clauses   : 443
% 0.48/0.66  # Clause-clause subsumption calls (NU) : 23696
% 0.48/0.66  # Rec. Clause-clause subsumption calls : 7987
% 0.48/0.66  # Non-unit clause-clause subsumptions  : 762
% 0.48/0.66  # Unit Clause-clause subsumption calls : 1319
% 0.48/0.66  # Rewrite failures with RHS unbound    : 0
% 0.48/0.66  # BW rewrite match attempts            : 50
% 0.48/0.66  # BW rewrite match successes           : 14
% 0.48/0.66  # Condensation attempts                : 0
% 0.48/0.66  # Condensation successes               : 0
% 0.48/0.66  # Termbank termtop insertions          : 464099
% 0.48/0.67  
% 0.48/0.67  # -------------------------------------------------
% 0.48/0.67  # User time                : 0.308 s
% 0.48/0.67  # System time              : 0.013 s
% 0.48/0.67  # Total time               : 0.322 s
% 0.48/0.67  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
