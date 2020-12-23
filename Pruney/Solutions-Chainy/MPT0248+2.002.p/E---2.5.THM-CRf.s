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
% DateTime   : Thu Dec  3 10:39:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  146 (2926177 expanded)
%              Number of clauses        :  111 (1255041 expanded)
%              Number of leaves         :   17 (818676 expanded)
%              Depth                    :   42
%              Number of atoms          :  296 (5070244 expanded)
%              Number of equality atoms :  120 (3325857 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_17,plain,(
    ! [X46,X47] : k3_tarski(k2_tarski(X46,X47)) = k2_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X31,X30)
        | X31 = X29
        | X30 != k1_tarski(X29) )
      & ( X32 != X29
        | r2_hidden(X32,X30)
        | X30 != k1_tarski(X29) )
      & ( ~ r2_hidden(esk4_2(X33,X34),X34)
        | esk4_2(X33,X34) != X33
        | X34 = k1_tarski(X33) )
      & ( r2_hidden(esk4_2(X33,X34),X34)
        | esk4_2(X33,X34) = X33
        | X34 = k1_tarski(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X48,X49,X50] :
      ( ( r2_hidden(X48,X50)
        | ~ r1_tarski(k2_tarski(X48,X49),X50) )
      & ( r2_hidden(X49,X50)
        | ~ r1_tarski(k2_tarski(X48,X49),X50) )
      & ( ~ r2_hidden(X48,X50)
        | ~ r2_hidden(X49,X50)
        | r1_tarski(k2_tarski(X48,X49),X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_24,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_xboole_0
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_39,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_40,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_28]),c_0_32]),c_0_33])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_28]),c_0_32]),c_0_33])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_32]),c_0_33])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_31]),c_0_28]),c_0_32]),c_0_33])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

fof(c_0_52,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_31]),c_0_28]),c_0_38]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_55,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_1(k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_1(k3_enumset1(X1,X1,X1,X1,X2)),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( esk1_1(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_38]),c_0_32]),c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk1_1(esk7_0) = esk5_0
    | r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_65,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_68,plain,(
    ! [X23,X24] : k4_xboole_0(k2_xboole_0(X23,X24),X24) = k4_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_1(esk6_0),esk6_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_67])).

fof(c_0_71,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_1(esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_38]),c_0_32]),c_0_33])).

fof(c_0_76,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_tarski(X28,X27) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_78,negated_conjecture,
    ( esk1_1(esk6_0) = esk5_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_73])).

cnf(c_0_79,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k4_xboole_0(X2,X1))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_38]),c_0_38]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) = k4_xboole_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_54])).

cnf(c_0_81,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_28]),c_0_32]),c_0_33])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_79])).

cnf(c_0_85,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_28]),c_0_28]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)
    | r2_hidden(esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_54])).

cnf(c_0_88,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_92,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_31]),c_0_28]),c_0_32]),c_0_33])).

fof(c_0_94,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk3_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_92])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk7_0)
    | r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( esk3_1(esk6_0) = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_102])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_107,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_108,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_105]),c_0_66])])).

cnf(c_0_109,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk6_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_31]),c_0_28]),c_0_32]),c_0_33])).

cnf(c_0_110,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_48])).

cnf(c_0_111,negated_conjecture,
    ( esk6_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk7_0 != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_31]),c_0_31]),c_0_28]),c_0_28]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | r2_hidden(esk2_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_90])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | esk7_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_111,c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),esk7_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_97])).

cnf(c_0_118,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_108])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_108]),c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk3_1(esk7_0),esk6_0)
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_122,negated_conjecture,
    ( esk2_2(esk6_0,esk7_0) = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | ~ r1_tarski(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_112]),c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( esk3_1(esk7_0) = esk5_0
    | r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_124]),c_0_125])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk3_1(X1),X1)
    | r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_97])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_90])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk1_1(X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_127]),c_0_50])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( esk1_1(esk7_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_134]),c_0_90])])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_135])).

cnf(c_0_137,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( r2_hidden(esk1_1(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_129])).

cnf(c_0_139,negated_conjecture,
    ( esk1_1(esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_1(X2)),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_129])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_139])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_139]),c_0_135])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_135])).

cnf(c_0_144,negated_conjecture,
    ( esk7_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_135]),c_0_135])])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_142]),c_0_143])]),c_0_144]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:36:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.41  # and selection function SelectNegativeLiterals.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.014 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.41  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.19/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.41  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.19/0.41  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.41  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.41  fof(c_0_17, plain, ![X46, X47]:k3_tarski(k2_tarski(X46,X47))=k2_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.41  fof(c_0_18, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_19, plain, ![X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X31,X30)|X31=X29|X30!=k1_tarski(X29))&(X32!=X29|r2_hidden(X32,X30)|X30!=k1_tarski(X29)))&((~r2_hidden(esk4_2(X33,X34),X34)|esk4_2(X33,X34)!=X33|X34=k1_tarski(X33))&(r2_hidden(esk4_2(X33,X34),X34)|esk4_2(X33,X34)=X33|X34=k1_tarski(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.41  fof(c_0_20, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_21, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  fof(c_0_22, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.41  fof(c_0_23, plain, ![X48, X49, X50]:(((r2_hidden(X48,X50)|~r1_tarski(k2_tarski(X48,X49),X50))&(r2_hidden(X49,X50)|~r1_tarski(k2_tarski(X48,X49),X50)))&(~r2_hidden(X48,X50)|~r2_hidden(X49,X50)|r1_tarski(k2_tarski(X48,X49),X50))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_24, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.19/0.41  fof(c_0_26, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.41  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_29, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_35, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  fof(c_0_36, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.41  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.41  fof(c_0_39, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_40, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_42, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_28]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_28]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_47, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_48, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_49, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_31]), c_0_28]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_50, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_51, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.19/0.41  fof(c_0_52, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.41  cnf(c_0_53, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_31]), c_0_28]), c_0_38]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.41  cnf(c_0_55, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.41  cnf(c_0_56, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_57, plain, (r2_hidden(esk1_1(k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_58, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_59, plain, (r2_hidden(esk1_1(k3_enumset1(X1,X1,X1,X1,X2)),k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_50, c_0_53])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.41  cnf(c_0_61, plain, (esk1_1(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_62, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_38]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (esk1_1(esk7_0)=esk5_0|r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.19/0.41  cnf(c_0_65, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (r1_tarski(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_54])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  fof(c_0_68, plain, ![X23, X24]:k4_xboole_0(k2_xboole_0(X23,X24),X24)=k4_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_1(esk6_0),esk6_0)|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_67])).
% 0.19/0.41  fof(c_0_71, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.41  cnf(c_0_72, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_1(esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.41  cnf(c_0_74, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.41  cnf(c_0_75, plain, (k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_38]), c_0_32]), c_0_33])).
% 0.19/0.41  fof(c_0_76, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_tarski(X28,X27), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.41  cnf(c_0_77, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (esk1_1(esk6_0)=esk5_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_73])).
% 0.19/0.41  cnf(c_0_79, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k4_xboole_0(X2,X1)))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_38]), c_0_38]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)=k4_xboole_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_75, c_0_54])).
% 0.19/0.41  cnf(c_0_81, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.41  cnf(c_0_82, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_28]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (r2_hidden(esk5_0,esk7_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_78])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_79])).
% 0.19/0.41  cnf(c_0_85, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_28]), c_0_28]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.41  cnf(c_0_86, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)|r2_hidden(esk5_0,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (k3_tarski(k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_54])).
% 0.19/0.41  cnf(c_0_88, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_86, c_0_83])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, (r1_tarski(esk7_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_87])).
% 0.19/0.41  cnf(c_0_91, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])])).
% 0.19/0.41  cnf(c_0_93, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_31]), c_0_28]), c_0_32]), c_0_33])).
% 0.19/0.41  fof(c_0_94, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk3_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.41  cnf(c_0_95, negated_conjecture, (r1_tarski(esk6_0,esk7_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_92])).
% 0.19/0.41  cnf(c_0_96, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_92])).
% 0.19/0.41  cnf(c_0_97, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.41  cnf(c_0_98, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_95])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.41  cnf(c_0_100, negated_conjecture, (X1=esk5_0|r2_hidden(esk5_0,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_92])).
% 0.19/0.41  cnf(c_0_101, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk7_0)|r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.41  cnf(c_0_102, negated_conjecture, (esk3_1(esk6_0)=esk5_0|r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_99, c_0_102])).
% 0.19/0.41  cnf(c_0_104, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_82, c_0_103])).
% 0.19/0.41  cnf(c_0_105, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_104, c_0_103])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_107, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_108, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|r2_hidden(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_105]), c_0_66])])).
% 0.19/0.41  cnf(c_0_109, negated_conjecture, (esk7_0!=k1_xboole_0|esk6_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_31]), c_0_28]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_110, plain, (X1=X2|r2_hidden(esk2_2(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_88, c_0_48])).
% 0.19/0.41  cnf(c_0_111, negated_conjecture, (esk6_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk7_0!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_31]), c_0_31]), c_0_28]), c_0_28]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.41  cnf(c_0_112, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_108])).
% 0.19/0.41  cnf(c_0_113, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_109, c_0_108])).
% 0.19/0.41  cnf(c_0_114, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|r2_hidden(esk2_2(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_110, c_0_90])).
% 0.19/0.41  cnf(c_0_115, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|esk7_0!=esk6_0), inference(spm,[status(thm)],[c_0_111, c_0_108])).
% 0.19/0.41  cnf(c_0_116, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_112])).
% 0.19/0.41  cnf(c_0_117, negated_conjecture, (r2_hidden(esk3_1(esk7_0),esk7_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_113, c_0_97])).
% 0.19/0.41  cnf(c_0_118, negated_conjecture, (X1=esk5_0|r2_hidden(esk5_0,k1_xboole_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_108])).
% 0.19/0.41  cnf(c_0_119, negated_conjecture, (r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_108]), c_0_115])).
% 0.19/0.41  cnf(c_0_120, negated_conjecture, (r2_hidden(esk3_1(esk7_0),esk6_0)|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.19/0.41  cnf(c_0_121, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_122, negated_conjecture, (esk2_2(esk6_0,esk7_0)=esk5_0|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.19/0.41  cnf(c_0_123, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|~r1_tarski(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_112]), c_0_115])).
% 0.19/0.41  cnf(c_0_124, negated_conjecture, (esk3_1(esk7_0)=esk5_0|r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_118, c_0_120])).
% 0.19/0.41  cnf(c_0_125, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|~r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_123])).
% 0.19/0.41  cnf(c_0_126, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_124]), c_0_125])).
% 0.19/0.41  cnf(c_0_127, negated_conjecture, (r2_hidden(esk3_1(X1),X1)|r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_126, c_0_97])).
% 0.19/0.41  cnf(c_0_128, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_90])).
% 0.19/0.41  cnf(c_0_129, negated_conjecture, (r2_hidden(esk1_1(X1),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_127]), c_0_50])).
% 0.19/0.41  cnf(c_0_130, negated_conjecture, (r2_hidden(esk1_1(esk7_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 0.19/0.41  cnf(c_0_131, negated_conjecture, (esk1_1(esk7_0)=esk5_0), inference(spm,[status(thm)],[c_0_56, c_0_130])).
% 0.19/0.41  cnf(c_0_132, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_129, c_0_131])).
% 0.19/0.41  cnf(c_0_133, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_132])).
% 0.19/0.41  cnf(c_0_134, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_132])).
% 0.19/0.41  cnf(c_0_135, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_134]), c_0_90])])).
% 0.19/0.41  cnf(c_0_136, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_69, c_0_135])).
% 0.19/0.41  cnf(c_0_137, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_135])).
% 0.19/0.41  cnf(c_0_138, negated_conjecture, (r2_hidden(esk1_1(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_136, c_0_129])).
% 0.19/0.41  cnf(c_0_139, negated_conjecture, (esk1_1(esk6_0)=esk5_0), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.19/0.41  cnf(c_0_140, negated_conjecture, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_1(X2)),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_82, c_0_129])).
% 0.19/0.41  cnf(c_0_141, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_129, c_0_139])).
% 0.19/0.41  cnf(c_0_142, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_139]), c_0_135])).
% 0.19/0.41  cnf(c_0_143, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_66, c_0_135])).
% 0.19/0.41  cnf(c_0_144, negated_conjecture, (esk7_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_135]), c_0_135])])).
% 0.19/0.41  cnf(c_0_145, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_142]), c_0_143])]), c_0_144]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 146
% 0.19/0.41  # Proof object clause steps            : 111
% 0.19/0.41  # Proof object formula steps           : 35
% 0.19/0.41  # Proof object conjectures             : 72
% 0.19/0.41  # Proof object clause conjectures      : 69
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 26
% 0.19/0.41  # Proof object initial formulas used   : 17
% 0.19/0.41  # Proof object generating inferences   : 64
% 0.19/0.41  # Proof object simplifying inferences  : 87
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 17
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 30
% 0.19/0.41  # Removed in clause preprocessing      : 5
% 0.19/0.41  # Initial clauses in saturation        : 25
% 0.19/0.41  # Processed clauses                    : 815
% 0.19/0.41  # ...of these trivial                  : 8
% 0.19/0.41  # ...subsumed                          : 436
% 0.19/0.41  # ...remaining for further processing  : 371
% 0.19/0.41  # Other redundant clauses eliminated   : 195
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 45
% 0.19/0.41  # Backward-rewritten                   : 158
% 0.19/0.41  # Generated clauses                    : 7036
% 0.19/0.41  # ...of the previous two non-trivial   : 6487
% 0.19/0.41  # Contextual simplify-reflections      : 11
% 0.19/0.41  # Paramodulations                      : 6841
% 0.19/0.41  # Factorizations                       : 1
% 0.19/0.41  # Equation resolutions                 : 195
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 140
% 0.19/0.41  #    Positive orientable unit clauses  : 27
% 0.19/0.41  #    Positive unorientable unit clauses: 1
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 110
% 0.19/0.41  # Current number of unprocessed clauses: 5663
% 0.19/0.41  # ...number of literals in the above   : 21090
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 232
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 8272
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 5102
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 466
% 0.19/0.41  # Unit Clause-clause subsumption calls : 1532
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 141
% 0.19/0.41  # BW rewrite match successes           : 71
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 108880
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.063 s
% 0.19/0.41  # System time              : 0.004 s
% 0.19/0.41  # Total time               : 0.067 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
