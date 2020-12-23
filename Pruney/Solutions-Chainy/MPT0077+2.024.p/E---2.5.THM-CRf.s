%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 417 expanded)
%              Number of clauses        :   45 ( 193 expanded)
%              Number of leaves         :   15 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  153 (1219 expanded)
%              Number of equality atoms :   32 ( 181 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_15,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

fof(c_0_21,plain,(
    ! [X23,X24] : k2_xboole_0(X23,k3_xboole_0(X23,X24)) = X23 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,
    ( ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk5_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X31,X32,X33] : r1_tarski(k2_xboole_0(k3_xboole_0(X31,X32),k3_xboole_0(X31,X33)),k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

fof(c_0_29,plain,(
    ! [X25,X26,X27] : k3_xboole_0(X25,k2_xboole_0(X26,X27)) = k2_xboole_0(k3_xboole_0(X25,X26),k3_xboole_0(X25,X27)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_30,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k2_xboole_0(X37,X38)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_31,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_32,plain,(
    ! [X28,X29,X30] : r1_tarski(k3_xboole_0(X28,X29),k2_xboole_0(X28,X30)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X39,X40] : k2_xboole_0(k3_xboole_0(X39,X40),k4_xboole_0(X39,X40)) = X39 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k2_xboole_0(X21,X22) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X41,X42,X43] :
      ( ~ r1_tarski(X41,X42)
      | ~ r1_xboole_0(X42,X43)
      | r1_xboole_0(X41,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_44,plain,(
    ! [X44,X45] : r1_tarski(X44,k2_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_45,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)
    | r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_55])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)
    | r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk5_0)
    | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_67])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_18]),c_0_42])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | k3_xboole_0(X1,X2) != k1_xboole_0
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_18]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.19/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.041 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.52  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.52  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.52  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.52  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.19/0.52  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.19/0.52  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.19/0.52  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.52  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.52  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 0.19/0.52  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.19/0.52  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.52  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.52  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.52  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.52  fof(c_0_15, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.52  fof(c_0_16, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.52  cnf(c_0_17, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  fof(c_0_19, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.52  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 0.19/0.52  fof(c_0_21, plain, ![X23, X24]:k2_xboole_0(X23,k3_xboole_0(X23,X24))=X23, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.19/0.52  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.52  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  fof(c_0_24, negated_conjecture, ((((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))))&((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|r1_xboole_0(esk3_0,esk4_0))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk4_0))))&((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|r1_xboole_0(esk3_0,esk5_0))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).
% 0.19/0.52  cnf(c_0_25, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  cnf(c_0_26, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.52  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  fof(c_0_28, plain, ![X31, X32, X33]:r1_tarski(k2_xboole_0(k3_xboole_0(X31,X32),k3_xboole_0(X31,X33)),k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.19/0.52  fof(c_0_29, plain, ![X25, X26, X27]:k3_xboole_0(X25,k2_xboole_0(X26,X27))=k2_xboole_0(k3_xboole_0(X25,X26),k3_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.19/0.52  fof(c_0_30, plain, ![X37, X38]:k4_xboole_0(X37,k2_xboole_0(X37,X38))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.52  fof(c_0_31, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.52  fof(c_0_32, plain, ![X28, X29, X30]:r1_tarski(k3_xboole_0(X28,X29),k2_xboole_0(X28,X30)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 0.19/0.52  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.19/0.52  cnf(c_0_34, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_26])).
% 0.19/0.52  cnf(c_0_35, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.52  cnf(c_0_36, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  fof(c_0_37, plain, ![X39, X40]:k2_xboole_0(k3_xboole_0(X39,X40),k4_xboole_0(X39,X40))=X39, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.19/0.52  cnf(c_0_38, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.52  cnf(c_0_39, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.52  fof(c_0_40, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k2_xboole_0(X21,X22)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.52  cnf(c_0_41, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.52  cnf(c_0_42, negated_conjecture, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.52  fof(c_0_43, plain, ![X41, X42, X43]:(~r1_tarski(X41,X42)|~r1_xboole_0(X42,X43)|r1_xboole_0(X41,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.19/0.52  fof(c_0_44, plain, ![X44, X45]:r1_tarski(X44,k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.52  fof(c_0_45, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.52  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.52  cnf(c_0_47, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.52  cnf(c_0_48, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.52  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  cnf(c_0_50, negated_conjecture, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.52  cnf(c_0_51, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.52  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.52  cnf(c_0_53, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.52  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_46, c_0_42])).
% 0.19/0.52  cnf(c_0_56, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_42])).
% 0.19/0.52  cnf(c_0_57, negated_conjecture, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.52  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.52  cnf(c_0_59, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)|r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.52  cnf(c_0_60, negated_conjecture, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_51, c_0_55])).
% 0.19/0.52  cnf(c_0_61, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_56]), c_0_57])).
% 0.19/0.52  cnf(c_0_62, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_53])).
% 0.19/0.52  cnf(c_0_63, negated_conjecture, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.52  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)|r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_27])).
% 0.19/0.52  cnf(c_0_65, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_62])).
% 0.19/0.52  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_53])).
% 0.19/0.52  cnf(c_0_68, negated_conjecture, (~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|~r1_xboole_0(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.19/0.52  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_67])).
% 0.19/0.52  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  cnf(c_0_71, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_18]), c_0_42])).
% 0.19/0.52  cnf(c_0_72, negated_conjecture, (~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.19/0.52  cnf(c_0_73, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|k3_xboole_0(X1,X2)!=k1_xboole_0|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.52  cnf(c_0_74, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_69])])).
% 0.19/0.52  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_18]), c_0_66])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 76
% 0.19/0.52  # Proof object clause steps            : 45
% 0.19/0.52  # Proof object formula steps           : 31
% 0.19/0.52  # Proof object conjectures             : 23
% 0.19/0.52  # Proof object clause conjectures      : 20
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 18
% 0.19/0.52  # Proof object initial formulas used   : 15
% 0.19/0.52  # Proof object generating inferences   : 24
% 0.19/0.52  # Proof object simplifying inferences  : 15
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 16
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 25
% 0.19/0.52  # Removed in clause preprocessing      : 3
% 0.19/0.52  # Initial clauses in saturation        : 22
% 0.19/0.52  # Processed clauses                    : 2351
% 0.19/0.52  # ...of these trivial                  : 34
% 0.19/0.52  # ...subsumed                          : 1906
% 0.19/0.52  # ...remaining for further processing  : 411
% 0.19/0.52  # Other redundant clauses eliminated   : 0
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 3
% 0.19/0.52  # Backward-rewritten                   : 55
% 0.19/0.52  # Generated clauses                    : 12288
% 0.19/0.52  # ...of the previous two non-trivial   : 8803
% 0.19/0.52  # Contextual simplify-reflections      : 8
% 0.19/0.52  # Paramodulations                      : 12288
% 0.19/0.52  # Factorizations                       : 0
% 0.19/0.52  # Equation resolutions                 : 0
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 331
% 0.19/0.52  #    Positive orientable unit clauses  : 70
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 6
% 0.19/0.52  #    Non-unit-clauses                  : 255
% 0.19/0.52  # Current number of unprocessed clauses: 6374
% 0.19/0.52  # ...number of literals in the above   : 14748
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 80
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 40070
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 33575
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 1517
% 0.19/0.52  # Unit Clause-clause subsumption calls : 268
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 81
% 0.19/0.52  # BW rewrite match successes           : 14
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 88860
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.174 s
% 0.19/0.52  # System time              : 0.004 s
% 0.19/0.52  # Total time               : 0.178 s
% 0.19/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
