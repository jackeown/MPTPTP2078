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
% DateTime   : Thu Dec  3 10:44:08 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (6227 expanded)
%              Number of clauses        :  100 (2505 expanded)
%              Number of leaves         :   20 (1852 expanded)
%              Depth                    :   24
%              Number of atoms          :  225 (7454 expanded)
%              Number of equality atoms :  161 (6964 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t126_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(c_0_20,plain,(
    ! [X53,X54] : k3_tarski(k2_tarski(X53,X54)) = k2_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X14,X15] : k3_xboole_0(X14,k2_xboole_0(X14,X15)) = X14 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k5_enumset1(X40,X40,X41,X42,X43,X44,X45) = k4_enumset1(X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52) = k5_enumset1(X46,X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,plain,(
    ! [X57,X58,X59,X60] : k4_xboole_0(k2_zfmisc_1(X57,X58),k2_zfmisc_1(X59,X60)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X57,X59),X58),k2_zfmisc_1(X57,k4_xboole_0(X58,X60))) ),
    inference(variable_rename,[status(thm)],[t126_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X55,X56] :
      ( ( k2_zfmisc_1(X55,X56) != k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( X55 != k1_xboole_0
        | k2_zfmisc_1(X55,X56) = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k2_zfmisc_1(X55,X56) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X4))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_33]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_45,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_46,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_47,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_52,plain,(
    ! [X23] : k5_xboole_0(X23,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_53,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_55,plain,(
    ! [X24,X25] : k2_xboole_0(X24,X25) = k5_xboole_0(X24,k4_xboole_0(X25,X24)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_56,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_57,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_50]),c_0_51]),c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_51,c_0_54])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_58]),c_0_50])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_60])).

fof(c_0_66,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k3_xboole_0(X16,X17) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_67,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_33]),c_0_40]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

fof(c_0_68,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_40])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_67]),c_0_50]),c_0_51])).

fof(c_0_76,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & ( ~ r1_tarski(esk1_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_71]),c_0_59])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_40])).

cnf(c_0_80,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_59])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_54])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X4)))
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_74]),c_0_58]),c_0_49]),c_0_58]),c_0_49]),c_0_58]),c_0_49]),c_0_58]),c_0_49]),c_0_58]),c_0_49]),c_0_58]),c_0_49]),c_0_58]),c_0_49]),c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,plain,
    ( X1 = X2
    | r1_tarski(X3,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_77]),c_0_51])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X3)) = k5_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_51])).

cnf(c_0_87,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),k1_xboole_0)
    | k5_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_50]),c_0_51])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)))) = k2_zfmisc_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_50]),c_0_51]),c_0_81]),c_0_50]),c_0_51]),c_0_67]),c_0_82]),c_0_54])).

cnf(c_0_89,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_57]),c_0_58])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_50]),c_0_51])).

cnf(c_0_92,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_75])).

cnf(c_0_94,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_95,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),X3) = X3
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)
    | ~ r1_tarski(X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_74]),c_0_58]),c_0_81]),c_0_67]),c_0_93]),c_0_60]),c_0_51])).

cnf(c_0_97,plain,
    ( k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)) = k1_xboole_0
    | k2_zfmisc_1(X2,X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_57])).

cnf(c_0_98,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(X3,k5_xboole_0(X4,k3_xboole_0(X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_94]),c_0_50]),c_0_51])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,X1) = X1
    | X2 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_70]),c_0_51])).

cnf(c_0_100,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k2_zfmisc_1(X1,X3)
    | k2_zfmisc_1(X4,X5) != k1_xboole_0
    | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_50]),c_0_51])).

cnf(c_0_101,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_95]),c_0_57])).

cnf(c_0_102,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k2_zfmisc_1(X1,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(X3,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_58])).

cnf(c_0_103,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_74]),c_0_58]),c_0_50])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_105,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(X3,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = X3
    | k5_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_87]),c_0_59])).

cnf(c_0_107,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_65,c_0_96])).

cnf(c_0_108,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_105])).

cnf(c_0_110,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | k5_xboole_0(X1,X2) != k1_xboole_0
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_79]),c_0_51])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1)) = k2_zfmisc_1(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_51])).

cnf(c_0_112,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,X3)) = k1_xboole_0
    | k5_xboole_0(X2,X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_87])).

cnf(c_0_113,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_42]),c_0_58])])).

cnf(c_0_114,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_54])).

cnf(c_0_115,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = X2
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) != k1_xboole_0
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_110,c_0_67])).

cnf(c_0_116,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_74]),c_0_58]),c_0_51])).

cnf(c_0_117,negated_conjecture,
    ( k5_xboole_0(X1,X2) != k1_xboole_0
    | ~ r1_tarski(esk2_0,k5_xboole_0(X1,X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_50]),c_0_84])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_113,c_0_67])).

cnf(c_0_119,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),k1_xboole_0)
    | k5_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_50]),c_0_51])).

cnf(c_0_120,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = X2
    | k5_xboole_0(X3,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_106]),c_0_59])).

cnf(c_0_121,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116])]),c_0_50]),c_0_51]),c_0_50]),c_0_51])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_108])).

cnf(c_0_123,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_124,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k5_xboole_0(X1,k5_xboole_0(X2,X3)) != k1_xboole_0
    | k5_xboole_0(X2,X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_59])).

cnf(c_0_125,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),X3)) = X3
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_79]),c_0_60])).

cnf(c_0_126,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k1_xboole_0)
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_121]),c_0_51]),c_0_84])).

cnf(c_0_127,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_93]),c_0_60]),c_0_51])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k3_xboole_0(X1,X2) != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125])]),c_0_51])).

cnf(c_0_130,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_122]),c_0_51])).

cnf(c_0_131,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_132,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_79,c_0_83])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_134,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_127]),c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_104]),c_0_133])])).

cnf(c_0_136,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_134]),c_0_81])])).

cnf(c_0_137,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_138,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_135]),c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_133])])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_138]),c_0_139]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.19/2.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.19/2.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.19/2.37  #
% 2.19/2.37  # Preprocessing time       : 0.027 s
% 2.19/2.37  # Presaturation interreduction done
% 2.19/2.37  
% 2.19/2.37  # Proof found!
% 2.19/2.37  # SZS status Theorem
% 2.19/2.37  # SZS output start CNFRefutation
% 2.19/2.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.19/2.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.19/2.37  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.19/2.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.19/2.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.19/2.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.19/2.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.19/2.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.19/2.37  fof(t126_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_zfmisc_1)).
% 2.19/2.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.19/2.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.19/2.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.19/2.37  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.19/2.37  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.19/2.37  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.19/2.37  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.19/2.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.19/2.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.19/2.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.19/2.37  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.19/2.37  fof(c_0_20, plain, ![X53, X54]:k3_tarski(k2_tarski(X53,X54))=k2_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 2.19/2.37  fof(c_0_21, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.19/2.37  fof(c_0_22, plain, ![X14, X15]:k3_xboole_0(X14,k2_xboole_0(X14,X15))=X14, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 2.19/2.37  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.19/2.37  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.19/2.37  fof(c_0_25, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.19/2.37  fof(c_0_26, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.19/2.37  fof(c_0_27, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.19/2.37  fof(c_0_28, plain, ![X40, X41, X42, X43, X44, X45]:k5_enumset1(X40,X40,X41,X42,X43,X44,X45)=k4_enumset1(X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 2.19/2.37  fof(c_0_29, plain, ![X46, X47, X48, X49, X50, X51, X52]:k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52)=k5_enumset1(X46,X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 2.19/2.37  fof(c_0_30, plain, ![X57, X58, X59, X60]:k4_xboole_0(k2_zfmisc_1(X57,X58),k2_zfmisc_1(X59,X60))=k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X57,X59),X58),k2_zfmisc_1(X57,k4_xboole_0(X58,X60))), inference(variable_rename,[status(thm)],[t126_zfmisc_1])).
% 2.19/2.37  fof(c_0_31, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.19/2.37  cnf(c_0_32, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.19/2.37  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 2.19/2.37  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.19/2.37  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.19/2.37  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.19/2.37  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.19/2.37  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.19/2.37  cnf(c_0_39, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.19/2.37  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.19/2.37  fof(c_0_41, plain, ![X55, X56]:((k2_zfmisc_1(X55,X56)!=k1_xboole_0|(X55=k1_xboole_0|X56=k1_xboole_0))&((X55!=k1_xboole_0|k2_zfmisc_1(X55,X56)=k1_xboole_0)&(X56!=k1_xboole_0|k2_zfmisc_1(X55,X56)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 2.19/2.37  cnf(c_0_42, plain, (k3_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 2.19/2.37  cnf(c_0_43, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X4)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_33]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 2.19/2.37  cnf(c_0_44, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.19/2.37  fof(c_0_45, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 2.19/2.37  fof(c_0_46, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 2.19/2.37  fof(c_0_47, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 2.19/2.37  cnf(c_0_48, plain, (k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.19/2.37  cnf(c_0_49, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_44])).
% 2.19/2.37  cnf(c_0_50, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.19/2.37  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.19/2.37  fof(c_0_52, plain, ![X23]:k5_xboole_0(X23,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 2.19/2.37  fof(c_0_53, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 2.19/2.37  cnf(c_0_54, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.19/2.37  fof(c_0_55, plain, ![X24, X25]:k2_xboole_0(X24,X25)=k5_xboole_0(X24,k4_xboole_0(X25,X24)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.19/2.37  fof(c_0_56, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 2.19/2.37  cnf(c_0_57, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2))=k2_zfmisc_1(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_50]), c_0_51]), c_0_50]), c_0_51])).
% 2.19/2.37  cnf(c_0_58, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 2.19/2.37  cnf(c_0_59, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.19/2.37  cnf(c_0_60, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_51, c_0_54])).
% 2.19/2.37  cnf(c_0_61, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 2.19/2.37  cnf(c_0_62, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 2.19/2.37  cnf(c_0_63, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.19/2.37  cnf(c_0_64, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X1)),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_58]), c_0_50])).
% 2.19/2.37  cnf(c_0_65, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_58]), c_0_60])).
% 2.19/2.37  fof(c_0_66, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k3_xboole_0(X16,X17)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.19/2.37  cnf(c_0_67, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_33]), c_0_40]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 2.19/2.37  fof(c_0_68, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 2.19/2.37  cnf(c_0_69, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_40])).
% 2.19/2.37  cnf(c_0_70, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0|X2=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 2.19/2.37  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_65, c_0_54])).
% 2.19/2.37  cnf(c_0_72, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 2.19/2.37  cnf(c_0_73, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.19/2.37  cnf(c_0_74, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 2.19/2.37  cnf(c_0_75, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_67]), c_0_50]), c_0_51])).
% 2.19/2.37  fof(c_0_76, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))&(k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).
% 2.19/2.37  cnf(c_0_77, plain, (X1=k1_xboole_0|r1_tarski(X2,X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 2.19/2.37  cnf(c_0_78, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_71]), c_0_59])).
% 2.19/2.37  cnf(c_0_79, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_40])).
% 2.19/2.37  cnf(c_0_80, plain, (r1_tarski(k5_xboole_0(X1,X2),X3)|k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_59])).
% 2.19/2.37  cnf(c_0_81, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_73])).
% 2.19/2.37  cnf(c_0_82, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_59, c_0_54])).
% 2.19/2.37  cnf(c_0_83, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X4)))|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_74]), c_0_58]), c_0_49]), c_0_58]), c_0_49]), c_0_58]), c_0_49]), c_0_58]), c_0_49]), c_0_58]), c_0_49]), c_0_58]), c_0_49]), c_0_58]), c_0_49]), c_0_75])).
% 2.19/2.37  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_76])).
% 2.19/2.37  cnf(c_0_85, plain, (X1=X2|r1_tarski(X3,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_77]), c_0_51])).
% 2.19/2.37  cnf(c_0_86, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X3))=k5_xboole_0(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_51])).
% 2.19/2.37  cnf(c_0_87, plain, (r1_tarski(k5_xboole_0(X1,X2),k1_xboole_0)|k5_xboole_0(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_50]), c_0_51])).
% 2.19/2.37  cnf(c_0_88, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2))))=k2_zfmisc_1(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_50]), c_0_51]), c_0_81]), c_0_50]), c_0_51]), c_0_67]), c_0_82]), c_0_54])).
% 2.19/2.37  cnf(c_0_89, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))=k1_xboole_0|~r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_57]), c_0_58])).
% 2.19/2.37  cnf(c_0_90, negated_conjecture, (r1_tarski(X1,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85])])).
% 2.19/2.37  cnf(c_0_91, plain, (k5_xboole_0(X1,X2)=X2|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_50]), c_0_51])).
% 2.19/2.37  cnf(c_0_92, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 2.19/2.37  cnf(c_0_93, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_75])).
% 2.19/2.37  cnf(c_0_94, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 2.19/2.37  cnf(c_0_95, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),X3)=X3|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 2.19/2.37  cnf(c_0_96, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)|~r1_tarski(X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_74]), c_0_58]), c_0_81]), c_0_67]), c_0_93]), c_0_60]), c_0_51])).
% 2.19/2.37  cnf(c_0_97, plain, (k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))=k1_xboole_0|k2_zfmisc_1(X2,X3)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_57])).
% 2.19/2.37  cnf(c_0_98, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k2_zfmisc_1(X1,X3)|~r1_tarski(X3,k5_xboole_0(X4,k3_xboole_0(X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_94]), c_0_50]), c_0_51])).
% 2.19/2.37  cnf(c_0_99, plain, (k3_xboole_0(X1,X1)=X1|X2=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_70]), c_0_51])).
% 2.19/2.37  cnf(c_0_100, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k2_zfmisc_1(X1,X3)|k2_zfmisc_1(X4,X5)!=k1_xboole_0|~r1_tarski(X3,k2_zfmisc_1(X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_50]), c_0_51])).
% 2.19/2.37  cnf(c_0_101, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_95]), c_0_57])).
% 2.19/2.37  cnf(c_0_102, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k2_zfmisc_1(X1,X3)|X4=k1_xboole_0|~r1_tarski(X3,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_58])).
% 2.19/2.37  cnf(c_0_103, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_74]), c_0_58]), c_0_50])).
% 2.19/2.37  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 2.19/2.37  cnf(c_0_105, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k2_zfmisc_1(X1,X3)|~r1_tarski(X3,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])).
% 2.19/2.37  cnf(c_0_106, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=X3|k5_xboole_0(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_87]), c_0_59])).
% 2.19/2.37  cnf(c_0_107, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2))=k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_65, c_0_96])).
% 2.19/2.37  cnf(c_0_108, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 2.19/2.37  cnf(c_0_109, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_105])).
% 2.19/2.37  cnf(c_0_110, plain, (X1=k3_xboole_0(X2,X3)|k5_xboole_0(X1,X2)!=k1_xboole_0|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_79]), c_0_51])).
% 2.19/2.37  cnf(c_0_111, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1))=k2_zfmisc_1(esk1_0,esk2_0)|~r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_51])).
% 2.19/2.37  cnf(c_0_112, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,X3))=k1_xboole_0|k5_xboole_0(X2,X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_109, c_0_87])).
% 2.19/2.37  cnf(c_0_113, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_42]), c_0_58])])).
% 2.19/2.37  cnf(c_0_114, plain, (r1_tarski(k5_xboole_0(X1,X2),X3)|k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_54])).
% 2.19/2.37  cnf(c_0_115, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=X2|k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))!=k1_xboole_0|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_110, c_0_67])).
% 2.19/2.37  cnf(c_0_116, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_74]), c_0_58]), c_0_51])).
% 2.19/2.37  cnf(c_0_117, negated_conjecture, (k5_xboole_0(X1,X2)!=k1_xboole_0|~r1_tarski(esk2_0,k5_xboole_0(X1,X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_50]), c_0_84])).
% 2.19/2.37  cnf(c_0_118, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_113, c_0_67])).
% 2.19/2.37  cnf(c_0_119, plain, (r1_tarski(k5_xboole_0(X1,X2),k1_xboole_0)|k5_xboole_0(X2,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_50]), c_0_51])).
% 2.19/2.37  cnf(c_0_120, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=X2|k5_xboole_0(X3,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_106]), c_0_59])).
% 2.19/2.37  cnf(c_0_121, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116])]), c_0_50]), c_0_51]), c_0_50]), c_0_51])).
% 2.19/2.37  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_108])).
% 2.19/2.37  cnf(c_0_123, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 2.19/2.37  cnf(c_0_124, plain, (r1_tarski(X1,k1_xboole_0)|k5_xboole_0(X1,k5_xboole_0(X2,X3))!=k1_xboole_0|k5_xboole_0(X2,X3)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_59])).
% 2.19/2.37  cnf(c_0_125, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),X3))=X3|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_79]), c_0_60])).
% 2.19/2.37  cnf(c_0_126, negated_conjecture, (~r1_tarski(esk1_0,k1_xboole_0)|~r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_121]), c_0_51]), c_0_84])).
% 2.19/2.37  cnf(c_0_127, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_122])).
% 2.19/2.37  cnf(c_0_128, negated_conjecture, (esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_93]), c_0_60]), c_0_51])).
% 2.19/2.37  cnf(c_0_129, plain, (r1_tarski(X1,k1_xboole_0)|k3_xboole_0(X1,X2)!=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125])]), c_0_51])).
% 2.19/2.37  cnf(c_0_130, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=esk1_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_122]), c_0_51])).
% 2.19/2.37  cnf(c_0_131, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 2.19/2.37  cnf(c_0_132, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_79, c_0_83])).
% 2.19/2.37  cnf(c_0_133, negated_conjecture, (r1_tarski(esk1_0,esk3_0)), inference(sr,[status(thm)],[c_0_127, c_0_128])).
% 2.19/2.37  cnf(c_0_134, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_127]), c_0_131])).
% 2.19/2.37  cnf(c_0_135, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_104]), c_0_133])])).
% 2.19/2.37  cnf(c_0_136, negated_conjecture, (esk1_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_134]), c_0_81])])).
% 2.19/2.37  cnf(c_0_137, negated_conjecture, (~r1_tarski(esk1_0,esk3_0)|~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 2.19/2.37  cnf(c_0_138, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_135]), c_0_136])).
% 2.19/2.37  cnf(c_0_139, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_133])])).
% 2.19/2.37  cnf(c_0_140, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_138]), c_0_139]), ['proof']).
% 2.19/2.37  # SZS output end CNFRefutation
% 2.19/2.37  # Proof object total steps             : 141
% 2.19/2.37  # Proof object clause steps            : 100
% 2.19/2.37  # Proof object formula steps           : 41
% 2.19/2.37  # Proof object conjectures             : 24
% 2.19/2.37  # Proof object clause conjectures      : 21
% 2.19/2.37  # Proof object formula conjectures     : 3
% 2.19/2.37  # Proof object initial clauses used    : 25
% 2.19/2.37  # Proof object initial formulas used   : 20
% 2.19/2.37  # Proof object generating inferences   : 64
% 2.19/2.37  # Proof object simplifying inferences  : 123
% 2.19/2.37  # Training examples: 0 positive, 0 negative
% 2.19/2.37  # Parsed axioms                        : 20
% 2.19/2.37  # Removed by relevancy pruning/SinE    : 0
% 2.19/2.37  # Initial clauses                      : 25
% 2.19/2.37  # Removed in clause preprocessing      : 8
% 2.19/2.37  # Initial clauses in saturation        : 17
% 2.19/2.37  # Processed clauses                    : 9549
% 2.19/2.37  # ...of these trivial                  : 323
% 2.19/2.37  # ...subsumed                          : 8296
% 2.19/2.37  # ...remaining for further processing  : 930
% 2.19/2.37  # Other redundant clauses eliminated   : 13317
% 2.19/2.37  # Clauses deleted for lack of memory   : 0
% 2.19/2.37  # Backward-subsumed                    : 56
% 2.19/2.37  # Backward-rewritten                   : 37
% 2.19/2.37  # Generated clauses                    : 193673
% 2.19/2.37  # ...of the previous two non-trivial   : 166310
% 2.19/2.37  # Contextual simplify-reflections      : 19
% 2.19/2.37  # Paramodulations                      : 180334
% 2.19/2.37  # Factorizations                       : 8
% 2.19/2.37  # Equation resolutions                 : 13317
% 2.19/2.37  # Propositional unsat checks           : 0
% 2.19/2.37  #    Propositional check models        : 0
% 2.19/2.37  #    Propositional check unsatisfiable : 0
% 2.19/2.37  #    Propositional clauses             : 0
% 2.19/2.37  #    Propositional clauses after purity: 0
% 2.19/2.37  #    Propositional unsat core size     : 0
% 2.19/2.37  #    Propositional preprocessing time  : 0.000
% 2.19/2.37  #    Propositional encoding time       : 0.000
% 2.19/2.37  #    Propositional solver time         : 0.000
% 2.19/2.37  #    Success case prop preproc time    : 0.000
% 2.19/2.37  #    Success case prop encoding time   : 0.000
% 2.19/2.37  #    Success case prop solver time     : 0.000
% 2.19/2.37  # Current number of processed clauses  : 804
% 2.19/2.37  #    Positive orientable unit clauses  : 67
% 2.19/2.37  #    Positive unorientable unit clauses: 26
% 2.19/2.37  #    Negative unit clauses             : 12
% 2.19/2.37  #    Non-unit-clauses                  : 699
% 2.19/2.37  # Current number of unprocessed clauses: 155834
% 2.19/2.37  # ...number of literals in the above   : 442691
% 2.19/2.37  # Current number of archived formulas  : 0
% 2.19/2.37  # Current number of archived clauses   : 132
% 2.19/2.37  # Clause-clause subsumption calls (NU) : 77945
% 2.19/2.37  # Rec. Clause-clause subsumption calls : 65356
% 2.19/2.37  # Non-unit clause-clause subsumptions  : 5873
% 2.19/2.37  # Unit Clause-clause subsumption calls : 540
% 2.19/2.37  # Rewrite failures with RHS unbound    : 19
% 2.19/2.37  # BW rewrite match attempts            : 1023
% 2.19/2.37  # BW rewrite match successes           : 215
% 2.19/2.37  # Condensation attempts                : 0
% 2.19/2.37  # Condensation successes               : 0
% 2.19/2.37  # Termbank termtop insertions          : 5234082
% 2.19/2.38  
% 2.19/2.38  # -------------------------------------------------
% 2.19/2.38  # User time                : 1.972 s
% 2.19/2.38  # System time              : 0.063 s
% 2.19/2.38  # Total time               : 2.035 s
% 2.19/2.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
