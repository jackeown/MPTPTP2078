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
% DateTime   : Thu Dec  3 10:44:53 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 216 expanded)
%              Number of clauses        :   47 (  99 expanded)
%              Number of leaves         :   12 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 ( 635 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ~ r1_xboole_0(X16,X17)
      | r1_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0))
    & r2_hidden(esk8_0,esk7_0)
    & r1_xboole_0(esk7_0,esk6_0)
    & ~ r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ( r1_xboole_0(X32,k2_xboole_0(X33,X34))
        | ~ r1_xboole_0(X32,X33)
        | ~ r1_xboole_0(X32,X34) )
      & ( r1_xboole_0(X32,X33)
        | ~ r1_xboole_0(X32,k2_xboole_0(X33,X34)) )
      & ( r1_xboole_0(X32,X34)
        | ~ r1_xboole_0(X32,k2_xboole_0(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0))
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X24,X25,X27,X28,X29] :
      ( ( r1_xboole_0(X24,X25)
        | r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)) )
      & ( ~ r2_hidden(X29,k3_xboole_0(X27,X28))
        | ~ r1_xboole_0(X27,X28) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_25,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0))
    | r2_hidden(esk2_2(esk6_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,esk7_0),esk6_0)
    | r2_hidden(esk2_2(esk6_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0))
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_2(k2_xboole_0(esk5_0,esk7_0),esk6_0),k3_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk7_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_33])).

fof(c_0_43,plain,(
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

fof(c_0_44,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | k3_xboole_0(X30,X31) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk6_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,X1),X1)
    | ~ r2_hidden(X2,k3_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,k2_xboole_0(esk5_0,esk7_0)),k3_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_50,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X37,X36)
        | X37 = X35
        | X36 != k1_tarski(X35) )
      & ( X38 != X35
        | r2_hidden(X38,X36)
        | X36 != k1_tarski(X35) )
      & ( ~ r2_hidden(esk4_2(X39,X40),X40)
        | esk4_2(X39,X40) != X39
        | X40 = k1_tarski(X39) )
      & ( r2_hidden(esk4_2(X39,X40),X40)
        | esk4_2(X39,X40) = X39
        | X40 = k1_tarski(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk5_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_33])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk6_0),k3_xboole_0(X1,esk6_0))
    | ~ r2_hidden(esk2_2(esk6_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk6_0,esk5_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) = k3_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k3_xboole_0(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_33])).

cnf(c_0_62,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))
    | ~ r2_hidden(X1,k3_xboole_0(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk3_2(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( esk3_2(esk5_0,esk6_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.07/1.23  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 1.07/1.23  # and selection function SelectCQArNTNpEqFirst.
% 1.07/1.23  #
% 1.07/1.23  # Preprocessing time       : 0.028 s
% 1.07/1.23  # Presaturation interreduction done
% 1.07/1.23  
% 1.07/1.23  # Proof found!
% 1.07/1.23  # SZS status Theorem
% 1.07/1.23  # SZS output start CNFRefutation
% 1.07/1.23  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 1.07/1.23  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.07/1.23  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.07/1.23  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.07/1.23  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.07/1.23  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.07/1.23  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.07/1.23  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.07/1.23  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.07/1.23  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.07/1.23  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.07/1.23  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.07/1.23  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 1.07/1.23  fof(c_0_13, plain, ![X16, X17]:(~r1_xboole_0(X16,X17)|r1_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.07/1.23  fof(c_0_14, negated_conjecture, (((r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0))&r2_hidden(esk8_0,esk7_0))&r1_xboole_0(esk7_0,esk6_0))&~r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 1.07/1.23  fof(c_0_15, plain, ![X32, X33, X34]:((r1_xboole_0(X32,k2_xboole_0(X33,X34))|~r1_xboole_0(X32,X33)|~r1_xboole_0(X32,X34))&((r1_xboole_0(X32,X33)|~r1_xboole_0(X32,k2_xboole_0(X33,X34)))&(r1_xboole_0(X32,X34)|~r1_xboole_0(X32,k2_xboole_0(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 1.07/1.23  cnf(c_0_16, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.07/1.23  cnf(c_0_17, negated_conjecture, (r1_xboole_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.23  cnf(c_0_18, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.07/1.23  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 1.07/1.23  fof(c_0_20, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk2_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk2_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.07/1.23  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0))|~r1_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.07/1.23  cnf(c_0_22, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.23  fof(c_0_23, plain, ![X24, X25, X27, X28, X29]:((r1_xboole_0(X24,X25)|r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)))&(~r2_hidden(X29,k3_xboole_0(X27,X28))|~r1_xboole_0(X27,X28))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.07/1.23  fof(c_0_24, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.07/1.23  fof(c_0_25, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.07/1.23  fof(c_0_26, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.07/1.23  fof(c_0_27, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.07/1.23  cnf(c_0_28, negated_conjecture, (r1_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0))|r2_hidden(esk2_2(esk6_0,X1),esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.07/1.23  cnf(c_0_29, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.23  cnf(c_0_30, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.07/1.23  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.07/1.23  cnf(c_0_32, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.23  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.07/1.23  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.23  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.07/1.23  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.07/1.23  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.07/1.23  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.23  cnf(c_0_39, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,esk7_0),esk6_0)|r2_hidden(esk2_2(esk6_0,X1),esk6_0)), inference(spm,[status(thm)],[c_0_16, c_0_28])).
% 1.07/1.23  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0))|r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_29])).
% 1.07/1.23  cnf(c_0_41, plain, (r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))|~r2_hidden(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.07/1.23  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_2(k2_xboole_0(esk5_0,esk7_0),esk6_0),k3_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk7_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_33])).
% 1.07/1.23  fof(c_0_43, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.07/1.23  fof(c_0_44, plain, ![X30, X31]:(~r1_tarski(X30,X31)|k3_xboole_0(X30,X31)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.07/1.23  cnf(c_0_45, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,esk6_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 1.07/1.23  cnf(c_0_46, plain, (r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 1.07/1.23  cnf(c_0_47, negated_conjecture, (r2_hidden(esk2_2(esk6_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_39])).
% 1.07/1.23  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_2(esk6_0,X1),X1)|~r2_hidden(X2,k3_xboole_0(esk6_0,k2_xboole_0(X1,esk7_0)))), inference(spm,[status(thm)],[c_0_30, c_0_40])).
% 1.07/1.23  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_2(esk6_0,k2_xboole_0(esk5_0,esk7_0)),k3_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk7_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.07/1.23  fof(c_0_50, plain, ![X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X37,X36)|X37=X35|X36!=k1_tarski(X35))&(X38!=X35|r2_hidden(X38,X36)|X36!=k1_tarski(X35)))&((~r2_hidden(esk4_2(X39,X40),X40)|esk4_2(X39,X40)!=X39|X40=k1_tarski(X39))&(r2_hidden(esk4_2(X39,X40),X40)|esk4_2(X39,X40)=X39|X40=k1_tarski(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.07/1.23  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.07/1.23  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.07/1.23  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_xboole_0(esk6_0,esk5_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[c_0_45, c_0_33])).
% 1.07/1.23  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.07/1.23  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_2(X1,esk6_0),k3_xboole_0(X1,esk6_0))|~r2_hidden(esk2_2(esk6_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.07/1.23  cnf(c_0_56, negated_conjecture, (r2_hidden(esk2_2(esk6_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.07/1.23  cnf(c_0_57, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.07/1.23  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_51])).
% 1.07/1.23  cnf(c_0_59, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk6_0,esk5_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))=k3_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.07/1.23  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_54])).
% 1.07/1.23  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),k3_xboole_0(esk6_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_33])).
% 1.07/1.23  cnf(c_0_62, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_35]), c_0_36]), c_0_37])).
% 1.07/1.23  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))|~r2_hidden(X1,k3_xboole_0(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.07/1.23  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_17])).
% 1.07/1.23  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.07/1.23  cnf(c_0_66, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_62])).
% 1.07/1.23  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_61])).
% 1.07/1.23  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk3_2(esk5_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.07/1.23  cnf(c_0_69, negated_conjecture, (esk3_2(esk5_0,esk6_0)=esk8_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.07/1.23  cnf(c_0_70, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.23  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_70])]), ['proof']).
% 1.07/1.23  # SZS output end CNFRefutation
% 1.07/1.23  # Proof object total steps             : 72
% 1.07/1.23  # Proof object clause steps            : 47
% 1.07/1.23  # Proof object formula steps           : 25
% 1.07/1.23  # Proof object conjectures             : 29
% 1.07/1.23  # Proof object clause conjectures      : 26
% 1.07/1.23  # Proof object formula conjectures     : 3
% 1.07/1.23  # Proof object initial clauses used    : 19
% 1.07/1.23  # Proof object initial formulas used   : 12
% 1.07/1.23  # Proof object generating inferences   : 21
% 1.07/1.23  # Proof object simplifying inferences  : 15
% 1.07/1.23  # Training examples: 0 positive, 0 negative
% 1.07/1.23  # Parsed axioms                        : 12
% 1.07/1.23  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.23  # Initial clauses                      : 28
% 1.07/1.23  # Removed in clause preprocessing      : 3
% 1.07/1.23  # Initial clauses in saturation        : 25
% 1.07/1.23  # Processed clauses                    : 4336
% 1.07/1.23  # ...of these trivial                  : 254
% 1.07/1.23  # ...subsumed                          : 1418
% 1.07/1.23  # ...remaining for further processing  : 2664
% 1.07/1.23  # Other redundant clauses eliminated   : 9
% 1.07/1.23  # Clauses deleted for lack of memory   : 0
% 1.07/1.23  # Backward-subsumed                    : 7
% 1.07/1.23  # Backward-rewritten                   : 113
% 1.07/1.23  # Generated clauses                    : 70821
% 1.07/1.23  # ...of the previous two non-trivial   : 66301
% 1.07/1.23  # Contextual simplify-reflections      : 0
% 1.07/1.23  # Paramodulations                      : 70783
% 1.07/1.23  # Factorizations                       : 30
% 1.07/1.23  # Equation resolutions                 : 9
% 1.07/1.23  # Propositional unsat checks           : 0
% 1.07/1.23  #    Propositional check models        : 0
% 1.07/1.23  #    Propositional check unsatisfiable : 0
% 1.07/1.23  #    Propositional clauses             : 0
% 1.07/1.23  #    Propositional clauses after purity: 0
% 1.07/1.23  #    Propositional unsat core size     : 0
% 1.07/1.23  #    Propositional preprocessing time  : 0.000
% 1.07/1.23  #    Propositional encoding time       : 0.000
% 1.07/1.23  #    Propositional solver time         : 0.000
% 1.07/1.23  #    Success case prop preproc time    : 0.000
% 1.07/1.23  #    Success case prop encoding time   : 0.000
% 1.07/1.23  #    Success case prop solver time     : 0.000
% 1.07/1.23  # Current number of processed clauses  : 2514
% 1.07/1.23  #    Positive orientable unit clauses  : 940
% 1.07/1.23  #    Positive unorientable unit clauses: 1
% 1.07/1.23  #    Negative unit clauses             : 617
% 1.07/1.23  #    Non-unit-clauses                  : 956
% 1.07/1.23  # Current number of unprocessed clauses: 61803
% 1.07/1.23  # ...number of literals in the above   : 132255
% 1.07/1.23  # Current number of archived formulas  : 0
% 1.07/1.23  # Current number of archived clauses   : 148
% 1.07/1.23  # Clause-clause subsumption calls (NU) : 145715
% 1.07/1.23  # Rec. Clause-clause subsumption calls : 136455
% 1.07/1.23  # Non-unit clause-clause subsumptions  : 515
% 1.07/1.23  # Unit Clause-clause subsumption calls : 127918
% 1.07/1.23  # Rewrite failures with RHS unbound    : 0
% 1.07/1.23  # BW rewrite match attempts            : 14336
% 1.07/1.23  # BW rewrite match successes           : 96
% 1.07/1.23  # Condensation attempts                : 0
% 1.07/1.23  # Condensation successes               : 0
% 1.07/1.23  # Termbank termtop insertions          : 1479376
% 1.07/1.24  
% 1.07/1.24  # -------------------------------------------------
% 1.07/1.24  # User time                : 0.838 s
% 1.07/1.24  # System time              : 0.041 s
% 1.07/1.24  # Total time               : 0.879 s
% 1.07/1.24  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
