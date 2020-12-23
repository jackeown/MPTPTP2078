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
% DateTime   : Thu Dec  3 10:44:33 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 719 expanded)
%              Number of clauses        :   37 ( 260 expanded)
%              Number of leaves         :   21 ( 228 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 757 expanded)
%              Number of equality atoms :   69 ( 708 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t144_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_21,plain,(
    ! [X60,X61] : k3_tarski(k2_tarski(X60,X61)) = k2_xboole_0(X60,X61) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X26,X27] : k3_xboole_0(X26,X27) = k5_xboole_0(k5_xboole_0(X26,X27),k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X34,X35,X36,X37] : k3_enumset1(X34,X34,X35,X36,X37) = k2_enumset1(X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t144_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X14,X15] : k4_xboole_0(k2_xboole_0(X14,X15),X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_30,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X38,X39,X40,X41,X42] : k4_enumset1(X38,X38,X39,X40,X41,X42) = k3_enumset1(X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X43,X44,X45,X46,X47,X48] : k5_enumset1(X43,X43,X44,X45,X46,X47,X48) = k4_enumset1(X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55] : k6_enumset1(X49,X49,X50,X51,X52,X53,X54,X55) = k5_enumset1(X49,X50,X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,plain,(
    ! [X16,X17,X18] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_39,plain,(
    ! [X56] : k3_tarski(k1_tarski(X56)) = X56 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_40,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X20,X21] :
      ( ~ r1_xboole_0(X20,X21)
      | k4_xboole_0(k2_xboole_0(X20,X21),X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

fof(c_0_42,plain,(
    ! [X57,X58,X59] :
      ( r2_hidden(X57,X58)
      | r2_hidden(X59,X58)
      | r1_xboole_0(k2_tarski(X57,X59),X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

fof(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0)
    & esk3_0 != k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_50,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_54,plain,(
    ! [X22,X23,X24] : k5_xboole_0(k5_xboole_0(X22,X23),X24) = k5_xboole_0(X22,k5_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_55,plain,(
    ! [X25] : k5_xboole_0(X25,X25) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_56,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_58,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 != k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_32]),c_0_45]),c_0_45]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_64,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_25]),c_0_33]),c_0_34]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_32]),c_0_45]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( r2_hidden(X3,X2)
    | r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_25]),c_0_33]),c_0_34]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 != k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_25]),c_0_45]),c_0_33]),c_0_34]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_62]),c_0_65])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = X2
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_62])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_65]),c_0_72])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = X3
    | r2_hidden(X1,X3)
    | r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.38  # and selection function SelectNegativeLiterals.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t144_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.20/0.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.38  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.38  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.20/0.38  fof(t57_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.20/0.38  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.20/0.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.38  fof(c_0_21, plain, ![X60, X61]:k3_tarski(k2_tarski(X60,X61))=k2_xboole_0(X60,X61), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.20/0.38  fof(c_0_22, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X26, X27]:k3_xboole_0(X26,X27)=k5_xboole_0(k5_xboole_0(X26,X27),k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.38  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  fof(c_0_26, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_27, plain, ![X34, X35, X36, X37]:k3_enumset1(X34,X34,X35,X36,X37)=k2_enumset1(X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t144_zfmisc_1])).
% 0.20/0.38  fof(c_0_29, plain, ![X14, X15]:k4_xboole_0(k2_xboole_0(X14,X15),X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.38  fof(c_0_30, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  fof(c_0_35, plain, ![X38, X39, X40, X41, X42]:k4_enumset1(X38,X38,X39,X40,X41,X42)=k3_enumset1(X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_36, plain, ![X43, X44, X45, X46, X47, X48]:k5_enumset1(X43,X43,X44,X45,X46,X47,X48)=k4_enumset1(X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.38  fof(c_0_37, plain, ![X49, X50, X51, X52, X53, X54, X55]:k6_enumset1(X49,X49,X50,X51,X52,X53,X54,X55)=k5_enumset1(X49,X50,X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.38  fof(c_0_38, plain, ![X16, X17, X18]:k2_xboole_0(k2_xboole_0(X16,X17),X18)=k2_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.38  fof(c_0_39, plain, ![X56]:k3_tarski(k1_tarski(X56))=X56, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.20/0.38  fof(c_0_40, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_41, plain, ![X20, X21]:(~r1_xboole_0(X20,X21)|k4_xboole_0(k2_xboole_0(X20,X21),X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.20/0.38  fof(c_0_42, plain, ![X57, X58, X59]:(r2_hidden(X57,X58)|r2_hidden(X59,X58)|r1_xboole_0(k2_tarski(X57,X59),X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_43, negated_conjecture, ((~r2_hidden(esk1_0,esk3_0)&~r2_hidden(esk2_0,esk3_0))&esk3_0!=k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 0.20/0.38  cnf(c_0_44, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.38  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_49, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  fof(c_0_50, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.20/0.38  cnf(c_0_51, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_52, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_53, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  fof(c_0_54, plain, ![X22, X23, X24]:k5_xboole_0(k5_xboole_0(X22,X23),X24)=k5_xboole_0(X22,k5_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.38  fof(c_0_55, plain, ![X25]:k5_xboole_0(X25,X25)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.38  fof(c_0_56, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.38  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  fof(c_0_58, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.38  cnf(c_0_59, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (esk3_0!=k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_61, plain, (k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2))))=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_32]), c_0_45]), c_0_45]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 0.20/0.38  cnf(c_0_62, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.38  cnf(c_0_63, plain, (k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 0.20/0.38  cnf(c_0_64, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_25]), c_0_33]), c_0_34]), c_0_47]), c_0_48]), c_0_49])).
% 0.20/0.38  cnf(c_0_65, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.38  cnf(c_0_66, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.38  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.38  cnf(c_0_68, plain, (k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_32]), c_0_45]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 0.20/0.38  cnf(c_0_69, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.38  cnf(c_0_70, plain, (r2_hidden(X3,X2)|r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_25]), c_0_33]), c_0_34]), c_0_47]), c_0_48]), c_0_49])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (esk3_0!=k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_25]), c_0_45]), c_0_33]), c_0_34]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49])).
% 0.20/0.38  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))=k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67]), c_0_62]), c_0_65])).
% 0.20/0.38  cnf(c_0_73, plain, (k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))=X2|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67]), c_0_62])).
% 0.20/0.38  cnf(c_0_74, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_65]), c_0_72])).
% 0.20/0.38  cnf(c_0_76, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=X3|r2_hidden(X1,X3)|r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_78, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 80
% 0.20/0.38  # Proof object clause steps            : 37
% 0.20/0.38  # Proof object formula steps           : 43
% 0.20/0.38  # Proof object conjectures             : 9
% 0.20/0.38  # Proof object clause conjectures      : 6
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 23
% 0.20/0.38  # Proof object initial formulas used   : 21
% 0.20/0.38  # Proof object generating inferences   : 3
% 0.20/0.38  # Proof object simplifying inferences  : 156
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 21
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 10
% 0.20/0.38  # Initial clauses in saturation        : 13
% 0.20/0.38  # Processed clauses                    : 292
% 0.20/0.38  # ...of these trivial                  : 70
% 0.20/0.38  # ...subsumed                          : 193
% 0.20/0.38  # ...remaining for further processing  : 29
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 502
% 0.20/0.38  # ...of the previous two non-trivial   : 385
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 502
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 27
% 0.20/0.38  #    Positive orientable unit clauses  : 14
% 0.20/0.38  #    Positive unorientable unit clauses: 4
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 6
% 0.20/0.38  # Current number of unprocessed clauses: 84
% 0.20/0.38  # ...number of literals in the above   : 120
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 12
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 7
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 3
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 10
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 79
% 0.20/0.38  # BW rewrite match successes           : 46
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 5750
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.035 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
