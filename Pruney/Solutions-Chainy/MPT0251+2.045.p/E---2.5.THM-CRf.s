%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 (1340 expanded)
%              Number of clauses        :   41 ( 560 expanded)
%              Number of leaves         :   18 ( 389 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 (1523 expanded)
%              Number of equality atoms :   61 (1202 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(c_0_18,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_19,plain,(
    ! [X26] : r1_xboole_0(X26,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_20,plain,(
    ! [X41,X42] : k3_tarski(k2_tarski(X41,X42)) = k2_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X22,X23] : k2_xboole_0(X22,k4_xboole_0(X23,X22)) = k2_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_26,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X35,X36,X37,X38] : k3_enumset1(X35,X35,X36,X37,X38) = k2_enumset1(X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_33,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_34,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_tarski(X28,X27) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_44,plain,(
    ! [X39,X40] :
      ( ( ~ r1_tarski(k1_tarski(X39),X40)
        | r2_hidden(X39,X40) )
      & ( ~ r2_hidden(X39,X40)
        | r1_tarski(k1_tarski(X39),X40) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_45,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_46,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

cnf(c_0_47,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_36]),c_0_38]),c_0_39])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    & k2_xboole_0(k1_tarski(esk3_0),esk4_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).

cnf(c_0_54,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_27]),c_0_27]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

fof(c_0_56,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_57,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_27]),c_0_38]),c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),X25) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_61,plain,
    ( k3_tarski(k3_enumset1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_61])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk3_0),esk4_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_71,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_66]),c_0_66]),c_0_66]),c_0_66])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_63,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_52]),c_0_27]),c_0_36]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_48]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_55])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_55]),c_0_71]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.20/0.37  # and selection function SelectCQIArNpEqFirst.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.028 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.37  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.37  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.37  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.20/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.37  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.37  fof(c_0_18, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.37  fof(c_0_19, plain, ![X26]:r1_xboole_0(X26,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.37  fof(c_0_20, plain, ![X41, X42]:k3_tarski(k2_tarski(X41,X42))=k2_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.37  fof(c_0_21, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.37  fof(c_0_22, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.37  cnf(c_0_23, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  fof(c_0_25, plain, ![X22, X23]:k2_xboole_0(X22,k4_xboole_0(X23,X22))=k2_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.37  cnf(c_0_26, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.37  fof(c_0_28, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.37  fof(c_0_29, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.37  fof(c_0_30, plain, ![X35, X36, X37, X38]:k3_enumset1(X35,X35,X36,X37,X38)=k2_enumset1(X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.37  cnf(c_0_31, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.37  cnf(c_0_32, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  fof(c_0_33, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.37  fof(c_0_34, plain, ![X19]:k2_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.37  cnf(c_0_35, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.37  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.37  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.37  cnf(c_0_40, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.37  cnf(c_0_41, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.37  cnf(c_0_42, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.37  fof(c_0_43, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_tarski(X28,X27), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.37  fof(c_0_44, plain, ![X39, X40]:((~r1_tarski(k1_tarski(X39),X40)|r2_hidden(X39,X40))&(~r2_hidden(X39,X40)|r1_tarski(k1_tarski(X39),X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.37  fof(c_0_45, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.37  fof(c_0_46, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 0.20/0.37  cnf(c_0_47, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.20/0.37  cnf(c_0_48, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.37  cnf(c_0_49, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_36]), c_0_38]), c_0_39])).
% 0.20/0.37  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.37  cnf(c_0_51, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.37  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.37  fof(c_0_53, negated_conjecture, (r2_hidden(esk3_0,esk4_0)&k2_xboole_0(k1_tarski(esk3_0),esk4_0)!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).
% 0.20/0.37  cnf(c_0_54, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.20/0.37  cnf(c_0_55, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_27]), c_0_27]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.20/0.37  fof(c_0_56, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.37  fof(c_0_57, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.37  cnf(c_0_58, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_27]), c_0_38]), c_0_39])).
% 0.20/0.37  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.37  fof(c_0_60, plain, ![X24, X25]:k4_xboole_0(k2_xboole_0(X24,X25),X25)=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.37  cnf(c_0_61, plain, (k3_tarski(k3_enumset1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),X1))=X1), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.37  cnf(c_0_62, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.37  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.37  cnf(c_0_64, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.37  cnf(c_0_65, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.37  cnf(c_0_66, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_61])).
% 0.20/0.37  cnf(c_0_67, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_62])).
% 0.20/0.37  cnf(c_0_68, negated_conjecture, (k2_xboole_0(k1_tarski(esk3_0),esk4_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.37  cnf(c_0_69, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.37  cnf(c_0_70, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.20/0.37  cnf(c_0_71, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_66]), c_0_66]), c_0_66]), c_0_66])).
% 0.20/0.37  cnf(c_0_72, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_63, c_0_67])).
% 0.20/0.37  cnf(c_0_73, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_52]), c_0_27]), c_0_36]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.20/0.37  cnf(c_0_74, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_47, c_0_69])).
% 0.20/0.37  cnf(c_0_75, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_48]), c_0_66])).
% 0.20/0.37  cnf(c_0_76, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))!=esk4_0), inference(rw,[status(thm)],[c_0_73, c_0_55])).
% 0.20/0.37  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_55]), c_0_71]), c_0_76]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 78
% 0.20/0.37  # Proof object clause steps            : 41
% 0.20/0.37  # Proof object formula steps           : 37
% 0.20/0.37  # Proof object conjectures             : 11
% 0.20/0.37  # Proof object clause conjectures      : 8
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 19
% 0.20/0.37  # Proof object initial formulas used   : 18
% 0.20/0.37  # Proof object generating inferences   : 11
% 0.20/0.37  # Proof object simplifying inferences  : 52
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 18
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 23
% 0.20/0.37  # Removed in clause preprocessing      : 6
% 0.20/0.37  # Initial clauses in saturation        : 17
% 0.20/0.37  # Processed clauses                    : 63
% 0.20/0.37  # ...of these trivial                  : 1
% 0.20/0.37  # ...subsumed                          : 7
% 0.20/0.37  # ...remaining for further processing  : 55
% 0.20/0.37  # Other redundant clauses eliminated   : 2
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 8
% 0.20/0.37  # Generated clauses                    : 73
% 0.20/0.37  # ...of the previous two non-trivial   : 55
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 71
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 2
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 29
% 0.20/0.37  #    Positive orientable unit clauses  : 16
% 0.20/0.37  #    Positive unorientable unit clauses: 1
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 10
% 0.20/0.37  # Current number of unprocessed clauses: 23
% 0.20/0.37  # ...number of literals in the above   : 32
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 30
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 9
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.37  # Unit Clause-clause subsumption calls : 10
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 49
% 0.20/0.37  # BW rewrite match successes           : 29
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 2243
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.026 s
% 0.20/0.37  # System time              : 0.008 s
% 0.20/0.37  # Total time               : 0.034 s
% 0.20/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
