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
% DateTime   : Thu Dec  3 10:41:32 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  107 (2414 expanded)
%              Number of clauses        :   71 ( 964 expanded)
%              Number of leaves         :   18 ( 722 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 (2772 expanded)
%              Number of equality atoms :   92 (2402 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t105_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & k4_xboole_0(X2,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_18,plain,(
    ! [X51,X52] : k3_tarski(k2_tarski(X51,X52)) = k2_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ~ r2_xboole_0(X16,X17)
      | k4_xboole_0(X17,X16) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).

fof(c_0_21,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k2_xboole_0(X19,X20)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k5_enumset1(X38,X38,X39,X40,X41,X42,X43) = k4_enumset1(X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50) = k5_enumset1(X44,X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

cnf(c_0_31,plain,
    ( ~ r2_xboole_0(X1,X2)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X22,X23] : k2_xboole_0(X22,X23) = k5_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_41,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

fof(c_0_42,plain,(
    ! [X12,X13] :
      ( ( k4_xboole_0(X12,X13) != k1_xboole_0
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | k4_xboole_0(X12,X13) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_43,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_44,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,X1)) != k1_xboole_0
    | ~ r2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32]),
    [final]).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_32]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),
    [final]).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

fof(c_0_52,plain,(
    ! [X21] : k5_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_53,plain,
    ( ~ r2_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46]),
    [final]).

cnf(c_0_54,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_34]),c_0_32]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_24]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

fof(c_0_56,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | ~ r2_xboole_0(X10,X11) )
      & ( X10 != X11
        | ~ r2_xboole_0(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | X10 = X11
        | r2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_32]),
    [final]).

cnf(c_0_58,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51]),
    [final]).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52]),
    [final]).

cnf(c_0_60,plain,
    ( ~ r2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_62,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56]),
    [final]).

cnf(c_0_63,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),
    [final]).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_xboole_0(k1_xboole_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63]),
    [final]).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_32]),
    [final]).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66]),
    [final]).

cnf(c_0_70,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51]),
    [final]).

cnf(c_0_71,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67]),
    [final]).

cnf(c_0_72,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | r2_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_68]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69]),
    [final]).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_54]),
    [final]).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_70]),
    [final]).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_54]),
    [final]).

cnf(c_0_77,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72]),
    [final]).

cnf(c_0_78,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_67]),c_0_59]),
    [final]).

cnf(c_0_79,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_50]),c_0_59]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))) = k3_tarski(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_69]),c_0_51]),
    [final]).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = esk1_0
    | r2_xboole_0(esk1_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_73]),
    [final]).

cnf(c_0_83,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_58]),c_0_59]),c_0_59]),
    [final]).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = X1
    | r2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_75]),
    [final]).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X1
    | r2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_76]),
    [final]).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = X1
    | ~ r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_70]),
    [final]).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_78]),
    [final]).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_78]),
    [final]).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X1
    | ~ r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_54]),
    [final]).

cnf(c_0_91,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = esk1_0
    | ~ r1_tarski(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_59]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = esk1_0
    | ~ r1_tarski(k3_tarski(k1_xboole_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_82]),
    [final]).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_51]),
    [final]).

cnf(c_0_95,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_66]),
    [final]).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) != k1_xboole_0
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_51]),
    [final]).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56]),
    [final]).

cnf(c_0_98,plain,
    ( ~ r2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_xboole_0(k3_tarski(k1_xboole_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_69]),
    [final]).

cnf(c_0_100,plain,
    ( ~ r2_xboole_0(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_58]),c_0_59])]),
    [final]).

cnf(c_0_101,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_83]),
    [final]).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_51]),
    [final]).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_84]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_tarski(k1_xboole_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_69]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_69]),c_0_69]),c_0_50]),c_0_59]),
    [final]).

cnf(c_0_106,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:00:01 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # No proof found!
% 0.12/0.36  # SZS status CounterSatisfiable
% 0.12/0.36  # SZS output start Saturation
% 0.12/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.36  fof(t105_xboole_1, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&k4_xboole_0(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 0.12/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.36  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.12/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.36  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.36  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.36  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.36  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.12/0.36  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.12/0.36  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.12/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.36  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.12/0.36  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.12/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.36  fof(c_0_18, plain, ![X51, X52]:k3_tarski(k2_tarski(X51,X52))=k2_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.36  fof(c_0_19, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.36  fof(c_0_20, plain, ![X16, X17]:(~r2_xboole_0(X16,X17)|k4_xboole_0(X17,X16)!=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).
% 0.12/0.36  fof(c_0_21, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.36  fof(c_0_22, plain, ![X19, X20]:k4_xboole_0(X19,k2_xboole_0(X19,X20))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.12/0.36  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  fof(c_0_25, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.36  fof(c_0_26, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.36  fof(c_0_27, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.36  fof(c_0_28, plain, ![X38, X39, X40, X41, X42, X43]:k5_enumset1(X38,X38,X39,X40,X41,X42,X43)=k4_enumset1(X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.36  fof(c_0_29, plain, ![X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50)=k5_enumset1(X44,X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.36  fof(c_0_30, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.12/0.36  cnf(c_0_31, plain, (~r2_xboole_0(X1,X2)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_33, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_34, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.36  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.36  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.36  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  fof(c_0_40, plain, ![X22, X23]:k2_xboole_0(X22,X23)=k5_xboole_0(X22,k4_xboole_0(X23,X22)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.12/0.36  fof(c_0_41, negated_conjecture, k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.12/0.36  fof(c_0_42, plain, ![X12, X13]:((k4_xboole_0(X12,X13)!=k1_xboole_0|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|k4_xboole_0(X12,X13)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.12/0.36  fof(c_0_43, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.36  fof(c_0_44, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.36  cnf(c_0_45, plain, (k5_xboole_0(X2,k3_xboole_0(X2,X1))!=k1_xboole_0|~r2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32]), ['final']).
% 0.12/0.36  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_32]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), ['final']).
% 0.12/0.36  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.36  cnf(c_0_49, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.36  cnf(c_0_50, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.12/0.36  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.12/0.36  fof(c_0_52, plain, ![X21]:k5_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.12/0.36  cnf(c_0_53, plain, (~r2_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46]), ['final']).
% 0.12/0.36  cnf(c_0_54, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_34]), c_0_32]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), ['final']).
% 0.12/0.36  cnf(c_0_55, negated_conjecture, (k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_24]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.12/0.36  fof(c_0_56, plain, ![X10, X11]:(((r1_tarski(X10,X11)|~r2_xboole_0(X10,X11))&(X10!=X11|~r2_xboole_0(X10,X11)))&(~r1_tarski(X10,X11)|X10=X11|r2_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.12/0.36  cnf(c_0_57, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_32]), ['final']).
% 0.12/0.36  cnf(c_0_58, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_59, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_52]), ['final']).
% 0.12/0.36  cnf(c_0_60, plain, (~r2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54]), ['final']).
% 0.12/0.36  cnf(c_0_61, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_55, c_0_54])).
% 0.12/0.36  cnf(c_0_62, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56]), ['final']).
% 0.12/0.36  cnf(c_0_63, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])]), ['final']).
% 0.12/0.36  cnf(c_0_64, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.36  cnf(c_0_65, negated_conjecture, (~r2_xboole_0(k1_xboole_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.12/0.36  cnf(c_0_66, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63]), ['final']).
% 0.12/0.36  cnf(c_0_67, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_32]), ['final']).
% 0.12/0.36  cnf(c_0_68, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_57, c_0_46]), ['final']).
% 0.12/0.36  cnf(c_0_69, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66]), ['final']).
% 0.12/0.36  cnf(c_0_70, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_54, c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_71, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_67]), ['final']).
% 0.12/0.36  cnf(c_0_72, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|r2_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_68]), ['final']).
% 0.12/0.36  cnf(c_0_73, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_68, c_0_69]), ['final']).
% 0.12/0.36  cnf(c_0_74, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_54]), ['final']).
% 0.12/0.36  cnf(c_0_75, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_68, c_0_70]), ['final']).
% 0.12/0.36  cnf(c_0_76, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_68, c_0_54]), ['final']).
% 0.12/0.36  cnf(c_0_77, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72]), ['final']).
% 0.12/0.36  cnf(c_0_78, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_67]), c_0_59]), ['final']).
% 0.12/0.36  cnf(c_0_79, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_50]), c_0_59]), ['final']).
% 0.12/0.36  cnf(c_0_80, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))=k3_tarski(k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_69]), c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_81, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_82, negated_conjecture, (k3_tarski(k1_xboole_0)=esk1_0|r2_xboole_0(esk1_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_62, c_0_73]), ['final']).
% 0.12/0.36  cnf(c_0_83, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.36  cnf(c_0_84, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_58]), c_0_59]), c_0_59]), ['final']).
% 0.12/0.36  cnf(c_0_85, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=X1|r2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_62, c_0_75]), ['final']).
% 0.12/0.36  cnf(c_0_86, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X1|r2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_62, c_0_76]), ['final']).
% 0.12/0.36  cnf(c_0_87, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=X1|~r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_77, c_0_70]), ['final']).
% 0.12/0.36  cnf(c_0_88, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_78]), ['final']).
% 0.12/0.36  cnf(c_0_89, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_54, c_0_78]), ['final']).
% 0.12/0.36  cnf(c_0_90, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X1|~r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_77, c_0_54]), ['final']).
% 0.12/0.36  cnf(c_0_91, plain, (k5_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_78]), ['final']).
% 0.12/0.36  cnf(c_0_92, negated_conjecture, (k3_tarski(k1_xboole_0)=esk1_0|~r1_tarski(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_59]), ['final']).
% 0.12/0.36  cnf(c_0_93, negated_conjecture, (k3_tarski(k1_xboole_0)=esk1_0|~r1_tarski(k3_tarski(k1_xboole_0),esk1_0)), inference(spm,[status(thm)],[c_0_71, c_0_82]), ['final']).
% 0.12/0.36  cnf(c_0_94, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_95, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_66]), ['final']).
% 0.12/0.36  cnf(c_0_96, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))!=k1_xboole_0|~r2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56]), ['final']).
% 0.12/0.36  cnf(c_0_98, plain, (~r2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_60, c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_99, negated_conjecture, (~r2_xboole_0(k3_tarski(k1_xboole_0),esk1_0)), inference(spm,[status(thm)],[c_0_53, c_0_69]), ['final']).
% 0.12/0.36  cnf(c_0_100, plain, (~r2_xboole_0(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_58]), c_0_59])]), ['final']).
% 0.12/0.36  cnf(c_0_101, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_83]), ['final']).
% 0.12/0.36  cnf(c_0_102, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_51]), ['final']).
% 0.12/0.36  cnf(c_0_103, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_57, c_0_84]), ['final']).
% 0.12/0.36  cnf(c_0_104, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_tarski(k1_xboole_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_69]), ['final']).
% 0.12/0.36  cnf(c_0_105, negated_conjecture, (k5_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_69]), c_0_69]), c_0_50]), c_0_59]), ['final']).
% 0.12/0.36  cnf(c_0_106, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0]), ['final']).
% 0.12/0.36  # SZS output end Saturation
% 0.12/0.36  # Proof object total steps             : 107
% 0.12/0.36  # Proof object clause steps            : 71
% 0.12/0.36  # Proof object formula steps           : 36
% 0.12/0.36  # Proof object conjectures             : 16
% 0.12/0.36  # Proof object clause conjectures      : 13
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 21
% 0.12/0.36  # Proof object initial formulas used   : 18
% 0.12/0.36  # Proof object generating inferences   : 40
% 0.12/0.36  # Proof object simplifying inferences  : 61
% 0.12/0.36  # Parsed axioms                        : 18
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 21
% 0.12/0.36  # Removed in clause preprocessing      : 8
% 0.12/0.36  # Initial clauses in saturation        : 13
% 0.12/0.36  # Processed clauses                    : 193
% 0.12/0.36  # ...of these trivial                  : 13
% 0.12/0.36  # ...subsumed                          : 107
% 0.12/0.36  # ...remaining for further processing  : 73
% 0.12/0.36  # Other redundant clauses eliminated   : 5
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 7
% 0.12/0.36  # Generated clauses                    : 293
% 0.12/0.36  # ...of the previous two non-trivial   : 168
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 288
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 5
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 52
% 0.12/0.36  #    Positive orientable unit clauses  : 19
% 0.12/0.36  #    Positive unorientable unit clauses: 3
% 0.12/0.36  #    Negative unit clauses             : 6
% 0.12/0.36  #    Non-unit-clauses                  : 24
% 0.12/0.36  # Current number of unprocessed clauses: 0
% 0.12/0.36  # ...number of literals in the above   : 0
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 28
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 120
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 116
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 55
% 0.12/0.36  # Unit Clause-clause subsumption calls : 19
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 36
% 0.12/0.36  # BW rewrite match successes           : 18
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 3663
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.031 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.036 s
% 0.12/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
