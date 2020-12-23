%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 806 expanded)
%              Number of clauses        :   49 ( 389 expanded)
%              Number of leaves         :   16 ( 207 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 (1000 expanded)
%              Number of equality atoms :   54 ( 684 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t144_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_16,plain,(
    ! [X48,X49] : k3_tarski(k2_tarski(X48,X49)) = k2_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_20,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k3_xboole_0(X24,X25)) = X24 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X36,X37] : k2_xboole_0(X36,X37) = k5_xboole_0(X36,k4_xboole_0(X37,X36)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k3_xboole_0(X22,X23))
      | r1_tarski(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_30,plain,(
    ! [X26] : k3_xboole_0(X26,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

fof(c_0_40,plain,(
    ! [X18,X19,X20] : k4_xboole_0(X18,k3_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X20)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_41,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_43])])).

fof(c_0_47,plain,(
    ! [X41,X42] : k2_tarski(X41,X42) = k2_tarski(X42,X41) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t144_zfmisc_1])).

fof(c_0_52,plain,(
    ! [X45,X46,X47] :
      ( r2_hidden(X45,X46)
      | r2_hidden(X47,X46)
      | r1_xboole_0(k2_tarski(X45,X47),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_33])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

fof(c_0_55,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_56,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_57,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_22]),c_0_22])).

fof(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0)
    & ~ r2_hidden(esk4_0,esk5_0)
    & esk5_0 != k4_xboole_0(esk5_0,k2_tarski(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_51])])])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_60,plain,(
    ! [X31,X32] : r1_tarski(X31,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_42]),c_0_35]),c_0_54])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_57]),c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(X3,X2)
    | r2_hidden(X1,X2)
    | r1_xboole_0(k1_enumset1(X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_22])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k4_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_61]),c_0_45]),c_0_49])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_64]),c_0_61]),c_0_46])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r1_xboole_0(k1_enumset1(esk4_0,esk4_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_27])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_57])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_33])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 != k4_xboole_0(esk5_0,k2_tarski(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) = X1
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_37])).

cnf(c_0_80,negated_conjecture,
    ( esk5_0 != k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S04AN
% 0.19/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.028 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.19/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.47  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.47  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.47  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.19/0.47  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.47  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.19/0.47  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.47  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 0.19/0.47  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.47  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.47  fof(t144_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.19/0.47  fof(t57_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.19/0.47  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.47  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.47  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.47  fof(c_0_16, plain, ![X48, X49]:k3_tarski(k2_tarski(X48,X49))=k2_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.19/0.47  fof(c_0_17, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.47  fof(c_0_18, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.47  fof(c_0_19, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.47  fof(c_0_20, plain, ![X24, X25]:k2_xboole_0(X24,k3_xboole_0(X24,X25))=X24, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.19/0.47  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  fof(c_0_23, plain, ![X36, X37]:k2_xboole_0(X36,X37)=k5_xboole_0(X36,k4_xboole_0(X37,X36)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.47  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_26, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.47  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  fof(c_0_29, plain, ![X21, X22, X23]:(~r1_tarski(X21,k3_xboole_0(X22,X23))|r1_tarski(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.19/0.47  fof(c_0_30, plain, ![X26]:k3_xboole_0(X26,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.47  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.47  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.47  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.19/0.47  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.47  cnf(c_0_35, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.19/0.47  cnf(c_0_37, plain, (k5_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X1))=X1), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.47  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.47  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 0.19/0.47  fof(c_0_40, plain, ![X18, X19, X20]:k4_xboole_0(X18,k3_xboole_0(X19,X20))=k2_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X20)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 0.19/0.47  fof(c_0_41, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.47  cnf(c_0_42, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 0.19/0.47  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.47  cnf(c_0_44, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.47  cnf(c_0_45, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.47  cnf(c_0_46, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_25]), c_0_43])])).
% 0.19/0.47  fof(c_0_47, plain, ![X41, X42]:k2_tarski(X41,X42)=k2_tarski(X42,X41), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.47  cnf(c_0_48, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k3_tarski(k1_enumset1(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_44, c_0_27])).
% 0.19/0.47  cnf(c_0_49, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.47  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  fof(c_0_51, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t144_zfmisc_1])).
% 0.19/0.47  fof(c_0_52, plain, ![X45, X46, X47]:(r2_hidden(X45,X46)|r2_hidden(X47,X46)|r1_xboole_0(k2_tarski(X45,X47),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).
% 0.19/0.47  cnf(c_0_53, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2)))=k4_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_48, c_0_33])).
% 0.19/0.47  cnf(c_0_54, plain, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.19/0.47  fof(c_0_55, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_56, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.47  cnf(c_0_57, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_22]), c_0_22])).
% 0.19/0.47  fof(c_0_58, negated_conjecture, ((~r2_hidden(esk3_0,esk5_0)&~r2_hidden(esk4_0,esk5_0))&esk5_0!=k4_xboole_0(esk5_0,k2_tarski(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_51])])])])).
% 0.19/0.47  cnf(c_0_59, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.47  fof(c_0_60, plain, ![X31, X32]:r1_tarski(X31,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.47  cnf(c_0_61, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_42]), c_0_35]), c_0_54])).
% 0.19/0.47  cnf(c_0_62, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.47  cnf(c_0_63, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.47  cnf(c_0_64, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_57]), c_0_33])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.47  cnf(c_0_66, plain, (r2_hidden(X3,X2)|r2_hidden(X1,X2)|r1_xboole_0(k1_enumset1(X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_59, c_0_22])).
% 0.19/0.47  cnf(c_0_67, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.47  cnf(c_0_68, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k4_xboole_0(X1,X2)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_25]), c_0_61]), c_0_45]), c_0_49])).
% 0.19/0.47  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.47  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_64]), c_0_61]), c_0_46])).
% 0.19/0.47  cnf(c_0_71, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,esk5_0)|r1_xboole_0(k1_enumset1(esk4_0,esk4_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.47  cnf(c_0_73, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_67, c_0_27])).
% 0.19/0.47  cnf(c_0_74, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X2,X3)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_57])).
% 0.19/0.47  cnf(c_0_76, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_73, c_0_33])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (esk5_0!=k4_xboole_0(esk5_0,k2_tarski(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (k4_xboole_0(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))=X1|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.47  cnf(c_0_79, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_76, c_0_37])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, (esk5_0!=k4_xboole_0(esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_77, c_0_22])).
% 0.19/0.47  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 82
% 0.19/0.47  # Proof object clause steps            : 49
% 0.19/0.47  # Proof object formula steps           : 33
% 0.19/0.47  # Proof object conjectures             : 11
% 0.19/0.47  # Proof object clause conjectures      : 8
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 18
% 0.19/0.47  # Proof object initial formulas used   : 16
% 0.19/0.47  # Proof object generating inferences   : 20
% 0.19/0.47  # Proof object simplifying inferences  : 26
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 20
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 26
% 0.19/0.47  # Removed in clause preprocessing      : 2
% 0.19/0.47  # Initial clauses in saturation        : 24
% 0.19/0.47  # Processed clauses                    : 518
% 0.19/0.47  # ...of these trivial                  : 15
% 0.19/0.47  # ...subsumed                          : 259
% 0.19/0.47  # ...remaining for further processing  : 244
% 0.19/0.47  # Other redundant clauses eliminated   : 10
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 5
% 0.19/0.47  # Backward-rewritten                   : 41
% 0.19/0.47  # Generated clauses                    : 4874
% 0.19/0.47  # ...of the previous two non-trivial   : 4136
% 0.19/0.47  # Contextual simplify-reflections      : 4
% 0.19/0.47  # Paramodulations                      : 4862
% 0.19/0.47  # Factorizations                       : 2
% 0.19/0.47  # Equation resolutions                 : 10
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 173
% 0.19/0.47  #    Positive orientable unit clauses  : 46
% 0.19/0.47  #    Positive unorientable unit clauses: 6
% 0.19/0.47  #    Negative unit clauses             : 16
% 0.19/0.47  #    Non-unit-clauses                  : 105
% 0.19/0.47  # Current number of unprocessed clauses: 3606
% 0.19/0.47  # ...number of literals in the above   : 6537
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 72
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 1326
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 1132
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 199
% 0.19/0.47  # Unit Clause-clause subsumption calls : 152
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 171
% 0.19/0.47  # BW rewrite match successes           : 66
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 97007
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.126 s
% 0.19/0.47  # System time              : 0.008 s
% 0.19/0.47  # Total time               : 0.134 s
% 0.19/0.47  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
