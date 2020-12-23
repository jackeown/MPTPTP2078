%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 484 expanded)
%              Number of clauses        :   39 ( 178 expanded)
%              Number of leaves         :   18 ( 152 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 499 expanded)
%              Number of equality atoms :   68 ( 476 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t58_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(k1_tarski(X1),X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(t132_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(c_0_18,plain,(
    ! [X78,X79] : k3_tarski(k2_tarski(X78,X79)) = k2_xboole_0(X78,X79) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X54,X55] : k1_enumset1(X54,X54,X55) = k2_tarski(X54,X55) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(k1_tarski(X1),X2)
        | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t58_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X15,X16] : k3_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X15,X16),k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X56,X57,X58] : k2_enumset1(X56,X56,X57,X58) = k1_enumset1(X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X59,X60,X61,X62] : k3_enumset1(X59,X59,X60,X61,X62) = k2_enumset1(X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0)
    & k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_27,plain,(
    ! [X53] : k2_tarski(X53,X53) = k1_tarski(X53) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X63,X64,X65,X66,X67] : k4_enumset1(X63,X63,X64,X65,X66,X67) = k3_enumset1(X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X68,X69,X70,X71,X72,X73] : k5_enumset1(X68,X68,X69,X70,X71,X72,X73) = k4_enumset1(X68,X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k5_enumset1(X46,X47,X48,X49,X50,X51,X52) = k2_xboole_0(k4_enumset1(X46,X47,X48,X49,X50,X51),k1_tarski(X52)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_35,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37,X38] : k7_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38) = k2_xboole_0(k4_enumset1(X30,X31,X32,X33,X34,X35),k1_enumset1(X36,X37,X38)) ),
    inference(variable_rename,[status(thm)],[t132_enumset1])).

fof(c_0_36,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] : k5_enumset1(X39,X40,X41,X42,X43,X44,X45) = k2_xboole_0(k1_enumset1(X39,X40,X41),k2_enumset1(X42,X43,X44,X45)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

fof(c_0_37,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28,X29] : k7_enumset1(X21,X22,X23,X24,X25,X26,X27,X28,X29) = k2_xboole_0(k3_enumset1(X21,X22,X23,X24,X25),k2_enumset1(X26,X27,X28,X29)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

fof(c_0_38,plain,(
    ! [X76,X77] :
      ( ~ r2_hidden(X76,X77)
      | k3_xboole_0(X77,k1_tarski(X76)) = k1_tarski(X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

fof(c_0_39,plain,(
    ! [X74,X75] :
      ( r2_hidden(X74,X75)
      | r1_xboole_0(k1_tarski(X74),X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_43,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_46,plain,(
    ! [X17,X18,X19,X20] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X20,X19,X18,X17) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_52,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0),k3_tarski(k5_enumset1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41]),c_0_23]),c_0_23]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_41]),c_0_23]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_59,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_60,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_61,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X7,X8,X9))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_29]),c_0_30]),c_0_31]),c_0_31]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k5_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_41]),c_0_41]),c_0_23]),c_0_23]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_41]),c_0_23]),c_0_30]),c_0_31]),c_0_43]),c_0_44])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_41]),c_0_23]),c_0_30]),c_0_31]),c_0_43]),c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk2_0,k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k3_tarski(k5_enumset1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_31]),c_0_31]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_68,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X7,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))) = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_63]),c_0_67])).

cnf(c_0_73,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X5,X5) = k5_enumset1(X1,X1,X1,X2,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))) = k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.29  % Computer   : n005.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 18:16:32 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  # Version: 2.5pre002
% 0.09/0.30  # No SInE strategy applied
% 0.09/0.30  # Trying AutoSched0 for 299 seconds
% 0.13/0.34  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.13/0.34  # and selection function SelectNegativeLiterals.
% 0.13/0.34  #
% 0.13/0.34  # Preprocessing time       : 0.027 s
% 0.13/0.34  
% 0.13/0.34  # Proof found!
% 0.13/0.34  # SZS status Theorem
% 0.13/0.34  # SZS output start CNFRefutation
% 0.13/0.34  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.34  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.13/0.34  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.13/0.34  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.34  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.34  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.34  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.34  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 0.13/0.34  fof(t132_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_enumset1)).
% 0.13/0.34  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 0.13/0.34  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 0.13/0.34  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.13/0.34  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.13/0.34  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.13/0.34  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.13/0.34  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.13/0.34  fof(c_0_18, plain, ![X78, X79]:k3_tarski(k2_tarski(X78,X79))=k2_xboole_0(X78,X79), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.34  fof(c_0_19, plain, ![X54, X55]:k1_enumset1(X54,X54,X55)=k2_tarski(X54,X55), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.34  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.13/0.34  fof(c_0_21, plain, ![X15, X16]:k3_xboole_0(X15,X16)=k5_xboole_0(k5_xboole_0(X15,X16),k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.13/0.34  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.34  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.34  fof(c_0_24, plain, ![X56, X57, X58]:k2_enumset1(X56,X56,X57,X58)=k1_enumset1(X56,X57,X58), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.34  fof(c_0_25, plain, ![X59, X60, X61, X62]:k3_enumset1(X59,X59,X60,X61,X62)=k2_enumset1(X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.34  fof(c_0_26, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)&k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.13/0.34  fof(c_0_27, plain, ![X53]:k2_tarski(X53,X53)=k1_tarski(X53), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.34  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.34  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.34  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.34  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.34  fof(c_0_32, plain, ![X63, X64, X65, X66, X67]:k4_enumset1(X63,X63,X64,X65,X66,X67)=k3_enumset1(X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.34  fof(c_0_33, plain, ![X68, X69, X70, X71, X72, X73]:k5_enumset1(X68,X68,X69,X70,X71,X72,X73)=k4_enumset1(X68,X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.34  fof(c_0_34, plain, ![X46, X47, X48, X49, X50, X51, X52]:k5_enumset1(X46,X47,X48,X49,X50,X51,X52)=k2_xboole_0(k4_enumset1(X46,X47,X48,X49,X50,X51),k1_tarski(X52)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 0.13/0.34  fof(c_0_35, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38]:k7_enumset1(X30,X31,X32,X33,X34,X35,X36,X37,X38)=k2_xboole_0(k4_enumset1(X30,X31,X32,X33,X34,X35),k1_enumset1(X36,X37,X38)), inference(variable_rename,[status(thm)],[t132_enumset1])).
% 0.13/0.34  fof(c_0_36, plain, ![X39, X40, X41, X42, X43, X44, X45]:k5_enumset1(X39,X40,X41,X42,X43,X44,X45)=k2_xboole_0(k1_enumset1(X39,X40,X41),k2_enumset1(X42,X43,X44,X45)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.13/0.34  fof(c_0_37, plain, ![X21, X22, X23, X24, X25, X26, X27, X28, X29]:k7_enumset1(X21,X22,X23,X24,X25,X26,X27,X28,X29)=k2_xboole_0(k3_enumset1(X21,X22,X23,X24,X25),k2_enumset1(X26,X27,X28,X29)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.13/0.34  fof(c_0_38, plain, ![X76, X77]:(~r2_hidden(X76,X77)|k3_xboole_0(X77,k1_tarski(X76))=k1_tarski(X76)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.13/0.34  fof(c_0_39, plain, ![X74, X75]:(r2_hidden(X74,X75)|r1_xboole_0(k1_tarski(X74),X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.13/0.34  cnf(c_0_40, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.34  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.34  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.13/0.34  cnf(c_0_43, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.34  cnf(c_0_44, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.34  fof(c_0_45, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.13/0.34  fof(c_0_46, plain, ![X17, X18, X19, X20]:k2_enumset1(X17,X18,X19,X20)=k2_enumset1(X20,X19,X18,X17), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.13/0.34  cnf(c_0_47, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.34  cnf(c_0_48, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.34  cnf(c_0_49, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.34  cnf(c_0_50, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.34  cnf(c_0_51, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.34  fof(c_0_52, plain, ![X12, X13, X14]:k5_xboole_0(k5_xboole_0(X12,X13),X14)=k5_xboole_0(X12,k5_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.13/0.34  cnf(c_0_53, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.34  cnf(c_0_54, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.34  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0),k3_tarski(k5_enumset1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41]), c_0_23]), c_0_23]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.13/0.34  cnf(c_0_56, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.34  cnf(c_0_57, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.34  cnf(c_0_58, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_41]), c_0_23]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.13/0.34  cnf(c_0_59, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.13/0.34  cnf(c_0_60, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.13/0.34  cnf(c_0_61, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X7,X8,X9)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_29]), c_0_30]), c_0_31]), c_0_31]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.13/0.34  cnf(c_0_62, plain, (k5_xboole_0(k5_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_41]), c_0_41]), c_0_23]), c_0_23]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.13/0.34  cnf(c_0_63, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.34  cnf(c_0_64, negated_conjecture, (~r1_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_41]), c_0_23]), c_0_30]), c_0_31]), c_0_43]), c_0_44])).
% 0.13/0.34  cnf(c_0_65, plain, (r2_hidden(X1,X2)|r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_41]), c_0_23]), c_0_30]), c_0_31]), c_0_43]), c_0_44])).
% 0.13/0.34  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk2_0,k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k3_tarski(k5_enumset1(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.34  cnf(c_0_67, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_31]), c_0_31]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.13/0.34  cnf(c_0_68, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X7,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.34  cnf(c_0_69, plain, (k7_enumset1(X1,X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.34  cnf(c_0_70, plain, (k5_xboole_0(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))))=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.34  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.34  cnf(c_0_72, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_63]), c_0_67])).
% 0.13/0.34  cnf(c_0_73, plain, (k5_enumset1(X1,X2,X3,X4,X5,X5,X5)=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.34  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.34  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_74])]), ['proof']).
% 0.13/0.34  # SZS output end CNFRefutation
% 0.13/0.34  # Proof object total steps             : 76
% 0.13/0.34  # Proof object clause steps            : 39
% 0.13/0.34  # Proof object formula steps           : 37
% 0.13/0.34  # Proof object conjectures             : 12
% 0.13/0.34  # Proof object clause conjectures      : 9
% 0.13/0.34  # Proof object formula conjectures     : 3
% 0.13/0.34  # Proof object initial clauses used    : 19
% 0.13/0.34  # Proof object initial formulas used   : 18
% 0.13/0.34  # Proof object generating inferences   : 3
% 0.13/0.34  # Proof object simplifying inferences  : 141
% 0.13/0.34  # Training examples: 0 positive, 0 negative
% 0.13/0.34  # Parsed axioms                        : 18
% 0.13/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.34  # Initial clauses                      : 19
% 0.13/0.35  # Removed in clause preprocessing      : 8
% 0.13/0.35  # Initial clauses in saturation        : 11
% 0.13/0.35  # Processed clauses                    : 435
% 0.13/0.35  # ...of these trivial                  : 313
% 0.13/0.35  # ...subsumed                          : 78
% 0.13/0.35  # ...remaining for further processing  : 44
% 0.13/0.35  # Other redundant clauses eliminated   : 0
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 0
% 0.13/0.35  # Backward-rewritten                   : 4
% 0.13/0.35  # Generated clauses                    : 1163
% 0.13/0.35  # ...of the previous two non-trivial   : 793
% 0.13/0.35  # Contextual simplify-reflections      : 0
% 0.13/0.35  # Paramodulations                      : 1163
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 0
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 40
% 0.13/0.35  #    Positive orientable unit clauses  : 27
% 0.13/0.35  #    Positive unorientable unit clauses: 10
% 0.13/0.35  #    Negative unit clauses             : 1
% 0.13/0.35  #    Non-unit-clauses                  : 2
% 0.13/0.35  # Current number of unprocessed clauses: 337
% 0.13/0.35  # ...number of literals in the above   : 339
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 12
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 2
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.35  # Unit Clause-clause subsumption calls : 62
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 279
% 0.13/0.35  # BW rewrite match successes           : 173
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 39401
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.051 s
% 0.13/0.35  # System time              : 0.001 s
% 0.13/0.35  # Total time               : 0.052 s
% 0.13/0.35  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
