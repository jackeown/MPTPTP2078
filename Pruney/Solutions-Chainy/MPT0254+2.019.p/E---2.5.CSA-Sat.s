%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:01 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  120 (12032 expanded)
%              Number of clauses        :   86 (4690 expanded)
%              Number of leaves         :   17 (3669 expanded)
%              Depth                    :   13
%              Number of atoms          :  190 (14020 expanded)
%              Number of equality atoms :   62 (10660 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t49_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X48,X49] : k3_tarski(k2_tarski(X48,X49)) = k2_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_22,negated_conjecture,(
    k2_xboole_0(k1_tarski(esk3_0),esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_23,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k1_enumset1(X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X33,X34,X35,X36] : k3_enumset1(X33,X33,X34,X35,X36) = k2_enumset1(X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X37,X38,X39,X40,X41] : k4_enumset1(X37,X37,X38,X39,X40,X41) = k3_enumset1(X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X42,X43,X44,X45,X46,X47] : k5_enumset1(X42,X42,X43,X44,X45,X46,X47) = k4_enumset1(X42,X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_tarski(X26,X25) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_31,plain,(
    ! [X23,X24] :
      ( ~ v1_xboole_0(X23)
      | X23 = X24
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

fof(c_0_34,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk3_0),esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_44,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33]),
    [final]).

fof(c_0_45,plain,(
    ! [X20] : r1_xboole_0(X20,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( k3_tarski(k5_enumset1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_25]),c_0_25]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),
    [final]).

cnf(c_0_49,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_xboole_0(X2,X3)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44]),
    [final]).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

fof(c_0_51,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( X1 = k3_xboole_0(X2,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0]),
    [final]).

fof(c_0_56,plain,(
    ! [X17] : k2_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55]),
    [final]).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [final]).

cnf(c_0_62,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61]),c_0_61])).

cnf(c_0_64,plain,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_62,c_0_48]),
    [final]).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_52]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_64]),
    [final]).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_62]),
    [final]).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | r2_hidden(esk2_2(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_67]),
    [final]).

cnf(c_0_71,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_68]),
    [final]).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55]),
    [final]).

cnf(c_0_74,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_69]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_tarski(k1_xboole_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_70]),
    [final]).

cnf(c_0_76,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_65]),
    [final]).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,X1)
    | r2_hidden(esk2_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_72]),
    [final]).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_44]),
    [final]).

cnf(c_0_79,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,k3_xboole_0(X1,X2))))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_48]),
    [final]).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_66,c_0_48]),
    [final]).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_72]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)))
    | ~ r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75]),
    [final]).

cnf(c_0_83,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_66]),
    [final]).

cnf(c_0_84,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_77]),
    [final]).

cnf(c_0_85,plain,
    ( v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_66]),
    [final]).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_66]),
    [final]).

cnf(c_0_87,plain,
    ( ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_66]),
    [final]).

cnf(c_0_88,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_64]),
    [final]).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_59]),c_0_50])]),
    [final]).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80]),
    [final]).

cnf(c_0_91,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_66]),
    [final]).

cnf(c_0_92,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_48]),
    [final]).

cnf(c_0_93,plain,
    ( X1 = X2
    | ~ r1_xboole_0(X2,X2)
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_81]),c_0_66]),
    [final]).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_80]),
    [final]).

cnf(c_0_95,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_66]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))
    | ~ r1_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_67]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,esk3_0)))
    | ~ r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_48]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( X1 = esk3_0
    | ~ r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_82]),c_0_66]),
    [final]).

cnf(c_0_99,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
    | r2_hidden(esk2_2(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_48]),
    [final]).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_48]),
    [final]).

cnf(c_0_101,plain,
    ( r1_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_80]),
    [final]).

cnf(c_0_102,plain,
    ( r1_xboole_0(X1,X1)
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_66]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_75]),
    [final]).

cnf(c_0_104,plain,
    ( v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_48]),
    [final]).

cnf(c_0_105,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_48]),
    [final]).

cnf(c_0_106,plain,
    ( ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_48]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))
    | r2_hidden(esk2_2(esk3_0,k3_tarski(k1_xboole_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_75]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_75]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_75]),
    [final]).

cnf(c_0_110,plain,
    ( r1_xboole_0(X1,X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_72]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_75]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_75]),
    [final]).

cnf(c_0_113,plain,
    ( v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_72]),
    [final]).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_72]),
    [final]).

cnf(c_0_115,plain,
    ( ~ r1_xboole_0(X1,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_72]),
    [final]).

cnf(c_0_116,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_78]),
    [final]).

cnf(c_0_117,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_64]),
    [final]).

cnf(c_0_118,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48]),
    [final]).

cnf(c_0_119,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_88]),c_0_89]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # No proof found!
% 0.12/0.38  # SZS status CounterSatisfiable
% 0.12/0.38  # SZS output start Saturation
% 0.12/0.38  fof(t49_zfmisc_1, conjecture, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.12/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.12/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.38  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.12/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.12/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t49_zfmisc_1])).
% 0.12/0.38  fof(c_0_18, plain, ![X48, X49]:k3_tarski(k2_tarski(X48,X49))=k2_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.38  fof(c_0_19, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_20, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.12/0.38  fof(c_0_21, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.38  fof(c_0_22, negated_conjecture, k2_xboole_0(k1_tarski(esk3_0),esk4_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.12/0.38  fof(c_0_23, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_26, plain, ![X30, X31, X32]:k2_enumset1(X30,X30,X31,X32)=k1_enumset1(X30,X31,X32), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_27, plain, ![X33, X34, X35, X36]:k3_enumset1(X33,X33,X34,X35,X36)=k2_enumset1(X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.38  fof(c_0_28, plain, ![X37, X38, X39, X40, X41]:k4_enumset1(X37,X37,X38,X39,X40,X41)=k3_enumset1(X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.38  fof(c_0_29, plain, ![X42, X43, X44, X45, X46, X47]:k5_enumset1(X42,X42,X43,X44,X45,X46,X47)=k4_enumset1(X42,X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.38  fof(c_0_30, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_tarski(X26,X25), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.38  fof(c_0_31, plain, ![X23, X24]:(~v1_xboole_0(X23)|X23=X24|~v1_xboole_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.12/0.38  cnf(c_0_32, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.12/0.38  cnf(c_0_33, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.12/0.38  fof(c_0_34, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k1_tarski(esk3_0),esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.38  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_42, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_43, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.12/0.38  cnf(c_0_44, plain, (v1_xboole_0(k3_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33]), ['final']).
% 0.12/0.38  fof(c_0_45, plain, ![X20]:r1_xboole_0(X20,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.12/0.38  cnf(c_0_46, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (k3_tarski(k5_enumset1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_25]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.12/0.38  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k5_enumset1(X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_25]), c_0_25]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), ['final']).
% 0.12/0.38  cnf(c_0_49, plain, (X1=k3_xboole_0(X2,X3)|~r1_xboole_0(X2,X3)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44]), ['final']).
% 0.12/0.38  cnf(c_0_50, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.12/0.38  fof(c_0_51, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.38  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), ['final']).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (k3_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.38  cnf(c_0_54, plain, (X1=k3_xboole_0(X2,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.38  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0]), ['final']).
% 0.12/0.38  fof(c_0_56, plain, ![X17]:k2_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.38  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51]), ['final']).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.38  cnf(c_0_59, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55]), ['final']).
% 0.12/0.38  cnf(c_0_60, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['final']).
% 0.12/0.38  cnf(c_0_62, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), ['final']).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61]), c_0_61])).
% 0.12/0.38  cnf(c_0_64, plain, (k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_62, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.12/0.38  cnf(c_0_66, plain, (k3_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))=X1), inference(spm,[status(thm)],[c_0_57, c_0_52]), ['final']).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_63, c_0_64]), ['final']).
% 0.12/0.38  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_62]), ['final']).
% 0.12/0.38  cnf(c_0_69, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|r2_hidden(esk2_2(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_52, c_0_67]), ['final']).
% 0.12/0.38  cnf(c_0_71, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.12/0.38  cnf(c_0_72, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_68]), ['final']).
% 0.12/0.38  cnf(c_0_73, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_43, c_0_55]), ['final']).
% 0.12/0.38  cnf(c_0_74, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X3)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_69]), ['final']).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk3_0,k3_tarski(k1_xboole_0))=esk3_0), inference(spm,[status(thm)],[c_0_57, c_0_70]), ['final']).
% 0.12/0.38  cnf(c_0_76, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_71, c_0_65]), ['final']).
% 0.12/0.38  cnf(c_0_77, plain, (r1_xboole_0(X1,X1)|r2_hidden(esk2_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_65, c_0_72]), ['final']).
% 0.12/0.38  cnf(c_0_78, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_44]), ['final']).
% 0.12/0.38  cnf(c_0_79, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,k3_xboole_0(X1,X2))))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_80, plain, (k3_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))=X1), inference(spm,[status(thm)],[c_0_66, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_81, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_74, c_0_72]), ['final']).
% 0.12/0.38  cnf(c_0_82, negated_conjecture, (r1_xboole_0(esk3_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)))|~r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_74, c_0_75]), ['final']).
% 0.12/0.38  cnf(c_0_83, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_76, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_84, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_77]), ['final']).
% 0.12/0.38  cnf(c_0_85, plain, (v1_xboole_0(X1)|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_44, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_86, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_78, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_87, plain, (~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_32, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_88, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_64]), ['final']).
% 0.12/0.38  cnf(c_0_89, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_59]), c_0_50])]), ['final']).
% 0.12/0.38  cnf(c_0_90, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1)))), inference(spm,[status(thm)],[c_0_79, c_0_80]), ['final']).
% 0.12/0.38  cnf(c_0_91, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3)))), inference(spm,[status(thm)],[c_0_79, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_92, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_81, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_93, plain, (X1=X2|~r1_xboole_0(X2,X2)|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_81]), c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_94, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1)))), inference(spm,[status(thm)],[c_0_74, c_0_80]), ['final']).
% 0.12/0.38  cnf(c_0_95, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3)))), inference(spm,[status(thm)],[c_0_74, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_96, negated_conjecture, (r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))|~r1_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_81, c_0_67]), ['final']).
% 0.12/0.38  cnf(c_0_97, negated_conjecture, (r1_xboole_0(esk3_0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,esk3_0)))|~r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_82, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_98, negated_conjecture, (X1=esk3_0|~r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_82]), c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_99, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))|r2_hidden(esk2_2(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))),X1)), inference(spm,[status(thm)],[c_0_69, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_100, plain, (r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_83, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_101, plain, (r1_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_84, c_0_80]), ['final']).
% 0.12/0.38  cnf(c_0_102, plain, (r1_xboole_0(X1,X1)|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_84, c_0_66]), ['final']).
% 0.12/0.38  cnf(c_0_103, negated_conjecture, (r1_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_84, c_0_75]), ['final']).
% 0.12/0.38  cnf(c_0_104, plain, (v1_xboole_0(X1)|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_85, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_105, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_86, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_106, plain, (~r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_87, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_107, negated_conjecture, (r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))|r2_hidden(esk2_2(esk3_0,k3_tarski(k1_xboole_0)),esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_75]), ['final']).
% 0.12/0.38  cnf(c_0_108, negated_conjecture, (~r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_75]), ['final']).
% 0.12/0.38  cnf(c_0_109, negated_conjecture, (r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_75]), ['final']).
% 0.12/0.38  cnf(c_0_110, plain, (r1_xboole_0(X1,X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_76, c_0_72]), ['final']).
% 0.12/0.38  cnf(c_0_111, negated_conjecture, (v1_xboole_0(esk3_0)|~r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_44, c_0_75]), ['final']).
% 0.12/0.38  cnf(c_0_112, negated_conjecture, (esk3_0=k1_xboole_0|~r1_xboole_0(esk3_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_78, c_0_75]), ['final']).
% 0.12/0.38  cnf(c_0_113, plain, (v1_xboole_0(X1)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_44, c_0_72]), ['final']).
% 0.12/0.38  cnf(c_0_114, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_78, c_0_72]), ['final']).
% 0.12/0.38  cnf(c_0_115, plain, (~r1_xboole_0(X1,X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_72]), ['final']).
% 0.12/0.38  cnf(c_0_116, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_78]), ['final']).
% 0.12/0.38  cnf(c_0_117, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_64]), ['final']).
% 0.12/0.38  cnf(c_0_118, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_52, c_0_48]), ['final']).
% 0.12/0.38  cnf(c_0_119, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_88]), c_0_89]), ['final']).
% 0.12/0.38  # SZS output end Saturation
% 0.12/0.38  # Proof object total steps             : 120
% 0.12/0.38  # Proof object clause steps            : 86
% 0.12/0.38  # Proof object formula steps           : 34
% 0.12/0.38  # Proof object conjectures             : 22
% 0.12/0.38  # Proof object clause conjectures      : 19
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 19
% 0.12/0.38  # Proof object initial formulas used   : 17
% 0.12/0.38  # Proof object generating inferences   : 59
% 0.12/0.38  # Proof object simplifying inferences  : 56
% 0.12/0.38  # Parsed axioms                        : 17
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 19
% 0.12/0.38  # Removed in clause preprocessing      : 7
% 0.12/0.38  # Initial clauses in saturation        : 12
% 0.12/0.38  # Processed clauses                    : 333
% 0.12/0.38  # ...of these trivial                  : 7
% 0.12/0.38  # ...subsumed                          : 238
% 0.12/0.38  # ...remaining for further processing  : 88
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 6
% 0.12/0.38  # Generated clauses                    : 418
% 0.12/0.38  # ...of the previous two non-trivial   : 310
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 418
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 69
% 0.12/0.38  #    Positive orientable unit clauses  : 18
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 49
% 0.12/0.38  # Current number of unprocessed clauses: 0
% 0.12/0.38  # ...number of literals in the above   : 0
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 26
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 1314
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 1022
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 232
% 0.12/0.38  # Unit Clause-clause subsumption calls : 11
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 29
% 0.12/0.38  # BW rewrite match successes           : 20
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4451
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.036 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.040 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
