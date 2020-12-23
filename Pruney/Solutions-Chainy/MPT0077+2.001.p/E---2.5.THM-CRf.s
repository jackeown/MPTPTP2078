%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:53 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 287 expanded)
%              Number of clauses        :   46 ( 128 expanded)
%              Number of leaves         :   14 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 520 expanded)
%              Number of equality atoms :   35 ( 162 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   15 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k2_xboole_0(X28,X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_16,plain,(
    ! [X30] : r1_tarski(k1_xboole_0,X30) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_17,plain,(
    ! [X41,X42,X43] :
      ( ~ r1_tarski(X41,X42)
      | ~ r1_xboole_0(X42,X43)
      | r1_xboole_0(X41,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_18,plain,(
    ! [X44,X45] : r1_tarski(X44,k2_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ r1_xboole_0(X18,X19)
      | r1_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_20,negated_conjecture,
    ( ( ~ r1_xboole_0(esk4_0,esk5_0)
      | ~ r1_xboole_0(esk4_0,esk6_0)
      | ~ r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) )
    & ( r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))
      | ~ r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) )
    & ( ~ r1_xboole_0(esk4_0,esk5_0)
      | ~ r1_xboole_0(esk4_0,esk6_0)
      | r1_xboole_0(esk4_0,esk5_0) )
    & ( r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))
      | r1_xboole_0(esk4_0,esk5_0) )
    & ( ~ r1_xboole_0(esk4_0,esk5_0)
      | ~ r1_xboole_0(esk4_0,esk6_0)
      | r1_xboole_0(esk4_0,esk6_0) )
    & ( r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))
      | r1_xboole_0(esk4_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_21,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))
    | r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)
    | r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))
    | r1_xboole_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_34,plain,(
    ! [X39,X40] : k2_xboole_0(k3_xboole_0(X39,X40),k4_xboole_0(X39,X40)) = X39 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_35,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k4_xboole_0(X37,X38)) = k3_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)
    | r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_33])).

fof(c_0_40,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X31,X32] : k2_xboole_0(X31,k4_xboole_0(X32,X31)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_44,plain,(
    ! [X34,X35,X36] : k4_xboole_0(k4_xboole_0(X34,X35),X36) = k4_xboole_0(X34,k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk5_0)
    | ~ r1_xboole_0(esk4_0,esk6_0)
    | ~ r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26])).

fof(c_0_49,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r1_xboole_0(X20,X21)
        | r2_hidden(esk2_2(X20,X21),k3_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_50,plain,(
    ! [X26] :
      ( X26 = k1_xboole_0
      | r2_hidden(esk3_1(X26),X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))
    | ~ r1_xboole_0(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_48])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_42]),c_0_42])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_28]),c_0_53]),c_0_28])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_42])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_59]),c_0_36])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_60]),c_0_28]),c_0_61])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_69,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_42])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k4_xboole_0(esk4_0,k4_xboole_0(k4_xboole_0(esk4_0,esk5_0),esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_54])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_1(k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_48]),c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_37]),c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_60]),c_0_60]),c_0_72]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.49/2.66  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.49/2.66  # and selection function SelectNegativeLiterals.
% 2.49/2.66  #
% 2.49/2.66  # Preprocessing time       : 0.027 s
% 2.49/2.66  # Presaturation interreduction done
% 2.49/2.66  
% 2.49/2.66  # Proof found!
% 2.49/2.66  # SZS status Theorem
% 2.49/2.66  # SZS output start CNFRefutation
% 2.49/2.66  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.49/2.66  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.49/2.66  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.49/2.66  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.49/2.66  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.49/2.66  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.49/2.66  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.49/2.66  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.49/2.66  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.49/2.66  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.49/2.66  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.49/2.66  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.49/2.66  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.49/2.66  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.49/2.66  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 2.49/2.66  fof(c_0_15, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k2_xboole_0(X28,X29)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.49/2.66  fof(c_0_16, plain, ![X30]:r1_tarski(k1_xboole_0,X30), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 2.49/2.66  fof(c_0_17, plain, ![X41, X42, X43]:(~r1_tarski(X41,X42)|~r1_xboole_0(X42,X43)|r1_xboole_0(X41,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 2.49/2.66  fof(c_0_18, plain, ![X44, X45]:r1_tarski(X44,k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.49/2.66  fof(c_0_19, plain, ![X18, X19]:(~r1_xboole_0(X18,X19)|r1_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 2.49/2.66  fof(c_0_20, negated_conjecture, ((((~r1_xboole_0(esk4_0,esk5_0)|~r1_xboole_0(esk4_0,esk6_0)|~r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)))&(r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))|~r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))))&((~r1_xboole_0(esk4_0,esk5_0)|~r1_xboole_0(esk4_0,esk6_0)|r1_xboole_0(esk4_0,esk5_0))&(r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))|r1_xboole_0(esk4_0,esk5_0))))&((~r1_xboole_0(esk4_0,esk5_0)|~r1_xboole_0(esk4_0,esk6_0)|r1_xboole_0(esk4_0,esk6_0))&(r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))|r1_xboole_0(esk4_0,esk6_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 2.49/2.66  fof(c_0_21, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.49/2.66  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.49/2.66  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.49/2.66  cnf(c_0_24, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.49/2.66  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.49/2.66  cnf(c_0_26, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.49/2.66  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))|r1_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.49/2.66  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.49/2.66  cnf(c_0_29, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 2.49/2.66  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.49/2.66  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)|r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.49/2.66  cnf(c_0_32, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 2.49/2.66  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))|r1_xboole_0(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.49/2.66  fof(c_0_34, plain, ![X39, X40]:k2_xboole_0(k3_xboole_0(X39,X40),k4_xboole_0(X39,X40))=X39, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 2.49/2.66  fof(c_0_35, plain, ![X37, X38]:k4_xboole_0(X37,k4_xboole_0(X37,X38))=k3_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.49/2.66  cnf(c_0_36, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.49/2.66  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_26])).
% 2.49/2.66  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 2.49/2.66  cnf(c_0_39, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)|r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_33])).
% 2.49/2.66  fof(c_0_40, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.49/2.66  cnf(c_0_41, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.49/2.66  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.49/2.66  fof(c_0_43, plain, ![X31, X32]:k2_xboole_0(X31,k4_xboole_0(X32,X31))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.49/2.66  fof(c_0_44, plain, ![X34, X35, X36]:k4_xboole_0(k4_xboole_0(X34,X35),X36)=k4_xboole_0(X34,k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.49/2.66  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 2.49/2.66  cnf(c_0_46, negated_conjecture, (~r1_xboole_0(esk4_0,esk5_0)|~r1_xboole_0(esk4_0,esk6_0)|~r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.49/2.66  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 2.49/2.66  cnf(c_0_48, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26])).
% 2.49/2.66  fof(c_0_49, plain, ![X20, X21, X23, X24, X25]:((r1_xboole_0(X20,X21)|r2_hidden(esk2_2(X20,X21),k3_xboole_0(X20,X21)))&(~r2_hidden(X25,k3_xboole_0(X23,X24))|~r1_xboole_0(X23,X24))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 2.49/2.66  fof(c_0_50, plain, ![X26]:(X26=k1_xboole_0|r2_hidden(esk3_1(X26),X26)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 2.49/2.66  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.49/2.66  cnf(c_0_52, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 2.49/2.66  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.49/2.66  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.49/2.66  cnf(c_0_55, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_45])).
% 2.49/2.66  cnf(c_0_56, negated_conjecture, (~r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))|~r1_xboole_0(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 2.49/2.66  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_48])).
% 2.49/2.66  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.49/2.66  cnf(c_0_59, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.49/2.66  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_42]), c_0_42])).
% 2.49/2.66  cnf(c_0_61, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_28]), c_0_53]), c_0_28])).
% 2.49/2.66  cnf(c_0_62, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 2.49/2.66  cnf(c_0_63, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.49/2.66  cnf(c_0_64, negated_conjecture, (~r1_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 2.49/2.66  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_58, c_0_42])).
% 2.49/2.66  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk3_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_59]), c_0_36])).
% 2.49/2.66  cnf(c_0_67, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_60]), c_0_28]), c_0_61])).
% 2.49/2.66  cnf(c_0_68, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 2.49/2.66  cnf(c_0_69, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_63, c_0_42])).
% 2.49/2.66  cnf(c_0_70, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k4_xboole_0(esk4_0,k4_xboole_0(k4_xboole_0(esk4_0,esk5_0),esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_54])).
% 2.49/2.66  cnf(c_0_71, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk3_1(k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_68])).
% 2.49/2.66  cnf(c_0_72, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_48]), c_0_60])).
% 2.49/2.66  cnf(c_0_73, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_37]), c_0_60])).
% 2.49/2.66  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_60]), c_0_60]), c_0_72]), c_0_73]), ['proof']).
% 2.49/2.66  # SZS output end CNFRefutation
% 2.49/2.66  # Proof object total steps             : 75
% 2.49/2.66  # Proof object clause steps            : 46
% 2.49/2.66  # Proof object formula steps           : 29
% 2.49/2.66  # Proof object conjectures             : 18
% 2.49/2.66  # Proof object clause conjectures      : 15
% 2.49/2.66  # Proof object formula conjectures     : 3
% 2.49/2.66  # Proof object initial clauses used    : 17
% 2.49/2.66  # Proof object initial formulas used   : 14
% 2.49/2.66  # Proof object generating inferences   : 22
% 2.49/2.66  # Proof object simplifying inferences  : 26
% 2.49/2.66  # Training examples: 0 positive, 0 negative
% 2.49/2.66  # Parsed axioms                        : 16
% 2.49/2.66  # Removed by relevancy pruning/SinE    : 0
% 2.49/2.66  # Initial clauses                      : 27
% 2.49/2.66  # Removed in clause preprocessing      : 4
% 2.49/2.66  # Initial clauses in saturation        : 23
% 2.49/2.66  # Processed clauses                    : 10962
% 2.49/2.66  # ...of these trivial                  : 646
% 2.49/2.66  # ...subsumed                          : 8915
% 2.49/2.66  # ...remaining for further processing  : 1401
% 2.49/2.66  # Other redundant clauses eliminated   : 3
% 2.49/2.66  # Clauses deleted for lack of memory   : 0
% 2.49/2.66  # Backward-subsumed                    : 75
% 2.49/2.66  # Backward-rewritten                   : 305
% 2.49/2.66  # Generated clauses                    : 372582
% 2.49/2.66  # ...of the previous two non-trivial   : 298075
% 2.49/2.66  # Contextual simplify-reflections      : 7
% 2.49/2.66  # Paramodulations                      : 372551
% 2.49/2.66  # Factorizations                       : 28
% 2.49/2.66  # Equation resolutions                 : 3
% 2.49/2.66  # Propositional unsat checks           : 0
% 2.49/2.66  #    Propositional check models        : 0
% 2.49/2.66  #    Propositional check unsatisfiable : 0
% 2.49/2.66  #    Propositional clauses             : 0
% 2.49/2.66  #    Propositional clauses after purity: 0
% 2.49/2.66  #    Propositional unsat core size     : 0
% 2.49/2.66  #    Propositional preprocessing time  : 0.000
% 2.49/2.66  #    Propositional encoding time       : 0.000
% 2.49/2.66  #    Propositional solver time         : 0.000
% 2.49/2.66  #    Success case prop preproc time    : 0.000
% 2.49/2.66  #    Success case prop encoding time   : 0.000
% 2.49/2.66  #    Success case prop solver time     : 0.000
% 2.49/2.66  # Current number of processed clauses  : 995
% 2.49/2.66  #    Positive orientable unit clauses  : 288
% 2.49/2.66  #    Positive unorientable unit clauses: 8
% 2.49/2.66  #    Negative unit clauses             : 173
% 2.49/2.66  #    Non-unit-clauses                  : 526
% 2.49/2.66  # Current number of unprocessed clauses: 286288
% 2.49/2.66  # ...number of literals in the above   : 983825
% 2.49/2.66  # Current number of archived formulas  : 0
% 2.49/2.66  # Current number of archived clauses   : 404
% 2.49/2.66  # Clause-clause subsumption calls (NU) : 61587
% 2.49/2.66  # Rec. Clause-clause subsumption calls : 44891
% 2.49/2.66  # Non-unit clause-clause subsumptions  : 3036
% 2.49/2.66  # Unit Clause-clause subsumption calls : 18554
% 2.49/2.66  # Rewrite failures with RHS unbound    : 0
% 2.49/2.66  # BW rewrite match attempts            : 1042
% 2.49/2.66  # BW rewrite match successes           : 284
% 2.49/2.66  # Condensation attempts                : 0
% 2.49/2.66  # Condensation successes               : 0
% 2.49/2.66  # Termbank termtop insertions          : 5658503
% 2.49/2.67  
% 2.49/2.67  # -------------------------------------------------
% 2.49/2.67  # User time                : 2.219 s
% 2.49/2.67  # System time              : 0.105 s
% 2.49/2.67  # Total time               : 2.324 s
% 2.49/2.67  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
