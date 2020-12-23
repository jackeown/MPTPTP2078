%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:51 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 171 expanded)
%              Number of clauses        :   52 (  78 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  177 ( 422 expanded)
%              Number of equality atoms :   54 ( 108 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))
    & r2_hidden(esk7_0,esk6_0)
    & r1_xboole_0(esk6_0,esk5_0)
    & ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_25,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X33
        | X34 != k1_tarski(X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k1_tarski(X33) )
      & ( ~ r2_hidden(esk3_2(X37,X38),X38)
        | esk3_2(X37,X38) != X37
        | X38 = k1_tarski(X37) )
      & ( r2_hidden(esk3_2(X37,X38),X38)
        | esk3_2(X37,X38) = X37
        | X38 = k1_tarski(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X25,X26] : r1_tarski(k4_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_37,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_38,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_41,plain,(
    ! [X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | k3_xboole_0(X13,X14) = k1_xboole_0 )
      & ( k3_xboole_0(X13,X14) != k1_xboole_0
        | r1_xboole_0(X13,X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))
    | r2_hidden(esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_47,plain,(
    ! [X29] : r1_xboole_0(X29,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)) = esk7_0
    | r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_45]),c_0_45])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk5_0,X1)
    | ~ r2_hidden(esk2_2(esk5_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)) = esk7_0
    | k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_58,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_59,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_54])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])]),c_0_50])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_53])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_70,plain,(
    ! [X30,X31,X32] :
      ( ( r1_xboole_0(X30,k2_xboole_0(X31,X32))
        | ~ r1_xboole_0(X30,X31)
        | ~ r1_xboole_0(X30,X32) )
      & ( r1_xboole_0(X30,X31)
        | ~ r1_xboole_0(X30,k2_xboole_0(X31,X32)) )
      & ( r1_xboole_0(X30,X32)
        | ~ r1_xboole_0(X30,k2_xboole_0(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_66]),c_0_67])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_35])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_xboole_0(X1,esk6_0))
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.90/4.10  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 3.90/4.10  # and selection function SelectCQArNTNpEqFirst.
% 3.90/4.10  #
% 3.90/4.10  # Preprocessing time       : 0.028 s
% 3.90/4.10  # Presaturation interreduction done
% 3.90/4.10  
% 3.90/4.10  # Proof found!
% 3.90/4.10  # SZS status Theorem
% 3.90/4.10  # SZS output start CNFRefutation
% 3.90/4.10  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.90/4.10  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.90/4.10  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.90/4.10  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.90/4.10  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.90/4.10  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.90/4.10  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.90/4.10  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.90/4.10  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.90/4.10  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.90/4.10  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.90/4.10  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.90/4.10  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.90/4.10  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.90/4.10  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.90/4.10  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 3.90/4.10  fof(c_0_16, negated_conjecture, (((r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))&r2_hidden(esk7_0,esk6_0))&r1_xboole_0(esk6_0,esk5_0))&~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 3.90/4.10  fof(c_0_17, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 3.90/4.10  fof(c_0_18, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.90/4.10  fof(c_0_19, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.90/4.10  cnf(c_0_20, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.90/4.10  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.90/4.10  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.90/4.10  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.90/4.10  fof(c_0_24, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.90/4.10  fof(c_0_25, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X35,X34)|X35=X33|X34!=k1_tarski(X33))&(X36!=X33|r2_hidden(X36,X34)|X34!=k1_tarski(X33)))&((~r2_hidden(esk3_2(X37,X38),X38)|esk3_2(X37,X38)!=X37|X38=k1_tarski(X37))&(r2_hidden(esk3_2(X37,X38),X38)|esk3_2(X37,X38)=X37|X38=k1_tarski(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 3.90/4.10  fof(c_0_26, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.90/4.10  cnf(c_0_27, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 3.90/4.10  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.90/4.10  cnf(c_0_29, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.90/4.10  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.90/4.10  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 3.90/4.10  fof(c_0_32, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 3.90/4.10  cnf(c_0_33, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_21]), c_0_22]), c_0_23])).
% 3.90/4.10  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|~r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 3.90/4.10  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.90/4.10  fof(c_0_36, plain, ![X25, X26]:r1_tarski(k4_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 3.90/4.10  fof(c_0_37, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.90/4.10  fof(c_0_38, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 3.90/4.10  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.90/4.10  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.90/4.10  fof(c_0_41, plain, ![X13, X14]:((~r1_xboole_0(X13,X14)|k3_xboole_0(X13,X14)=k1_xboole_0)&(k3_xboole_0(X13,X14)!=k1_xboole_0|r1_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 3.90/4.10  cnf(c_0_42, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_33])).
% 3.90/4.10  cnf(c_0_43, negated_conjecture, (r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))|r2_hidden(esk2_2(X1,k3_xboole_0(esk5_0,esk4_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 3.90/4.10  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.90/4.10  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.90/4.10  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.90/4.10  fof(c_0_47, plain, ![X29]:r1_xboole_0(X29,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 3.90/4.10  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 3.90/4.10  cnf(c_0_49, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.90/4.10  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.90/4.10  cnf(c_0_51, negated_conjecture, (esk2_2(X1,k3_xboole_0(esk5_0,esk4_0))=esk7_0|r1_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 3.90/4.10  cnf(c_0_52, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 3.90/4.10  cnf(c_0_53, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_45]), c_0_45])).
% 3.90/4.10  cnf(c_0_54, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 3.90/4.10  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk5_0,X1)|~r2_hidden(esk2_2(esk5_0,X1),esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 3.90/4.10  cnf(c_0_56, negated_conjecture, (esk2_2(X1,k3_xboole_0(esk5_0,esk4_0))=esk7_0|k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 3.90/4.10  cnf(c_0_57, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.90/4.10  fof(c_0_58, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.90/4.10  cnf(c_0_59, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 3.90/4.10  cnf(c_0_60, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_54])).
% 3.90/4.10  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.90/4.10  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])]), c_0_50])).
% 3.90/4.10  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 3.90/4.10  cnf(c_0_64, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 3.90/4.10  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 3.90/4.10  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 3.90/4.10  cnf(c_0_67, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_63, c_0_53])).
% 3.90/4.10  cnf(c_0_68, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 3.90/4.10  cnf(c_0_69, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.90/4.10  fof(c_0_70, plain, ![X30, X31, X32]:((r1_xboole_0(X30,k2_xboole_0(X31,X32))|~r1_xboole_0(X30,X31)|~r1_xboole_0(X30,X32))&((r1_xboole_0(X30,X31)|~r1_xboole_0(X30,k2_xboole_0(X31,X32)))&(r1_xboole_0(X30,X32)|~r1_xboole_0(X30,k2_xboole_0(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 3.90/4.10  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_66]), c_0_67])).
% 3.90/4.10  cnf(c_0_72, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 3.90/4.10  cnf(c_0_73, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 3.90/4.10  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_35])).
% 3.90/4.10  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 3.90/4.10  cnf(c_0_76, negated_conjecture, (r1_xboole_0(esk5_0,k2_xboole_0(X1,esk6_0))|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 3.90/4.10  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_75])).
% 3.90/4.10  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 3.90/4.10  cnf(c_0_79, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_28])).
% 3.90/4.10  cnf(c_0_80, negated_conjecture, (k3_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_78])).
% 3.90/4.10  cnf(c_0_81, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.90/4.10  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), ['proof']).
% 3.90/4.10  # SZS output end CNFRefutation
% 3.90/4.10  # Proof object total steps             : 83
% 3.90/4.10  # Proof object clause steps            : 52
% 3.90/4.10  # Proof object formula steps           : 31
% 3.90/4.10  # Proof object conjectures             : 25
% 3.90/4.10  # Proof object clause conjectures      : 22
% 3.90/4.10  # Proof object formula conjectures     : 3
% 3.90/4.10  # Proof object initial clauses used    : 22
% 3.90/4.10  # Proof object initial formulas used   : 15
% 3.90/4.10  # Proof object generating inferences   : 24
% 3.90/4.10  # Proof object simplifying inferences  : 16
% 3.90/4.10  # Training examples: 0 positive, 0 negative
% 3.90/4.10  # Parsed axioms                        : 16
% 3.90/4.10  # Removed by relevancy pruning/SinE    : 0
% 3.90/4.10  # Initial clauses                      : 31
% 3.90/4.10  # Removed in clause preprocessing      : 4
% 3.90/4.10  # Initial clauses in saturation        : 27
% 3.90/4.10  # Processed clauses                    : 16149
% 3.90/4.10  # ...of these trivial                  : 629
% 3.90/4.10  # ...subsumed                          : 7638
% 3.90/4.10  # ...remaining for further processing  : 7882
% 3.90/4.10  # Other redundant clauses eliminated   : 41
% 3.90/4.10  # Clauses deleted for lack of memory   : 0
% 3.90/4.10  # Backward-subsumed                    : 9
% 3.90/4.10  # Backward-rewritten                   : 67
% 3.90/4.10  # Generated clauses                    : 376770
% 3.90/4.10  # ...of the previous two non-trivial   : 346277
% 3.90/4.10  # Contextual simplify-reflections      : 3
% 3.90/4.10  # Paramodulations                      : 376667
% 3.90/4.10  # Factorizations                       : 63
% 3.90/4.10  # Equation resolutions                 : 41
% 3.90/4.10  # Propositional unsat checks           : 1
% 3.90/4.10  #    Propositional check models        : 1
% 3.90/4.10  #    Propositional check unsatisfiable : 0
% 3.90/4.10  #    Propositional clauses             : 0
% 3.90/4.10  #    Propositional clauses after purity: 0
% 3.90/4.10  #    Propositional unsat core size     : 0
% 3.90/4.10  #    Propositional preprocessing time  : 0.000
% 3.90/4.10  #    Propositional encoding time       : 0.076
% 3.90/4.10  #    Propositional solver time         : 0.009
% 3.90/4.10  #    Success case prop preproc time    : 0.000
% 3.90/4.10  #    Success case prop encoding time   : 0.000
% 3.90/4.10  #    Success case prop solver time     : 0.000
% 3.90/4.10  # Current number of processed clauses  : 7776
% 3.90/4.10  #    Positive orientable unit clauses  : 4107
% 3.90/4.10  #    Positive unorientable unit clauses: 1
% 3.90/4.10  #    Negative unit clauses             : 918
% 3.90/4.10  #    Non-unit-clauses                  : 2750
% 3.90/4.10  # Current number of unprocessed clauses: 330047
% 3.90/4.10  # ...number of literals in the above   : 580364
% 3.90/4.10  # Current number of archived formulas  : 0
% 3.90/4.10  # Current number of archived clauses   : 106
% 3.90/4.10  # Clause-clause subsumption calls (NU) : 2362272
% 3.90/4.10  # Rec. Clause-clause subsumption calls : 2316014
% 3.90/4.10  # Non-unit clause-clause subsumptions  : 4333
% 3.90/4.10  # Unit Clause-clause subsumption calls : 632168
% 3.90/4.10  # Rewrite failures with RHS unbound    : 0
% 3.90/4.10  # BW rewrite match attempts            : 928858
% 3.90/4.10  # BW rewrite match successes           : 28
% 3.90/4.10  # Condensation attempts                : 0
% 3.90/4.10  # Condensation successes               : 0
% 3.90/4.10  # Termbank termtop insertions          : 9967530
% 3.90/4.12  
% 3.90/4.12  # -------------------------------------------------
% 3.90/4.12  # User time                : 3.597 s
% 3.90/4.12  # System time              : 0.170 s
% 3.90/4.12  # Total time               : 3.767 s
% 3.90/4.12  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
