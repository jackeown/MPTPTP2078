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
% DateTime   : Thu Dec  3 10:44:05 EST 2020

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  114 (1728 expanded)
%              Number of clauses        :   69 ( 695 expanded)
%              Number of leaves         :   22 ( 506 expanded)
%              Depth                    :   16
%              Number of atoms          :  176 (2268 expanded)
%              Number of equality atoms :  131 (1860 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(c_0_22,plain,(
    ! [X79,X80,X81] :
      ( k2_zfmisc_1(k4_xboole_0(X79,X80),X81) = k4_xboole_0(k2_zfmisc_1(X79,X81),k2_zfmisc_1(X80,X81))
      & k2_zfmisc_1(X81,k4_xboole_0(X79,X80)) = k4_xboole_0(k2_zfmisc_1(X81,X79),k2_zfmisc_1(X81,X80)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X75,X76,X77,X78] : k2_zfmisc_1(k3_xboole_0(X75,X76),k3_xboole_0(X77,X78)) = k3_xboole_0(k2_zfmisc_1(X75,X77),k2_zfmisc_1(X76,X78)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_26,plain,(
    ! [X65,X66] : k3_tarski(k2_tarski(X65,X66)) = k2_xboole_0(X65,X66) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_33,plain,(
    ! [X72,X73,X74] :
      ( k2_zfmisc_1(k2_xboole_0(X72,X73),X74) = k2_xboole_0(k2_zfmisc_1(X72,X74),k2_zfmisc_1(X73,X74))
      & k2_zfmisc_1(X74,k2_xboole_0(X72,X73)) = k2_xboole_0(k2_zfmisc_1(X74,X72),k2_zfmisc_1(X74,X73)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_37,plain,(
    ! [X43,X44,X45,X46] : k3_enumset1(X43,X43,X44,X45,X46) = k2_enumset1(X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_38,plain,(
    ! [X47,X48,X49,X50,X51] : k4_enumset1(X47,X47,X48,X49,X50,X51) = k3_enumset1(X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_39,plain,(
    ! [X52,X53,X54,X55,X56,X57] : k5_enumset1(X52,X52,X53,X54,X55,X56,X57) = k4_enumset1(X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_40,plain,(
    ! [X58,X59,X60,X61,X62,X63,X64] : k6_enumset1(X58,X58,X59,X60,X61,X62,X63,X64) = k5_enumset1(X58,X59,X60,X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_41,plain,(
    ! [X67,X68] :
      ( ( k2_zfmisc_1(X67,X68) != k1_xboole_0
        | X67 = k1_xboole_0
        | X68 = k1_xboole_0 )
      & ( X67 != k1_xboole_0
        | k2_zfmisc_1(X67,X68) = k1_xboole_0 )
      & ( X68 != k1_xboole_0
        | k2_zfmisc_1(X67,X68) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_44,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k3_xboole_0(X27,X28) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_45,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_53,plain,(
    ! [X36,X37] : k2_tarski(X36,X37) = k2_tarski(X37,X36) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_54,plain,(
    ! [X69,X70,X71] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X70,X69),k2_zfmisc_1(X71,X69))
        | X69 = k1_xboole_0
        | r1_tarski(X70,X71) )
      & ( ~ r1_tarski(k2_zfmisc_1(X69,X70),k2_zfmisc_1(X69,X71))
        | X69 = k1_xboole_0
        | r1_tarski(X70,X71) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_61,plain,(
    ! [X25,X26] : k2_xboole_0(X25,k3_xboole_0(X25,X26)) = X25 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_62,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) = k2_zfmisc_1(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_67,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5)))) = k2_zfmisc_1(k3_xboole_0(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_xboole_0(X4,X5)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_30])).

cnf(c_0_68,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_35]),c_0_35]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_71,plain,(
    ! [X21,X22] :
      ( ( k4_xboole_0(X21,X22) != k1_xboole_0
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | k4_xboole_0(X21,X22) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X2,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_75,negated_conjecture,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),X1))) = k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_65]),c_0_68])).

cnf(c_0_76,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

fof(c_0_77,plain,(
    ! [X35] : k5_xboole_0(X35,X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_78,plain,(
    ! [X30] : r1_tarski(k1_xboole_0,X30) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_29]),c_0_29])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(esk3_0,esk5_0),k1_xboole_0)
    | ~ r1_tarski(k5_xboole_0(k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,esk4_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_76])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_81,c_0_29])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(esk3_0,esk5_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85])])).

fof(c_0_89,plain,(
    ! [X29] : k3_xboole_0(X29,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X4)),k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_30])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk5_0),k1_xboole_0)
    | r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_80]),c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)),k3_xboole_0(esk4_0,esk6_0)) = k5_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_65])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | r1_tarski(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_91]),c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)))
    | k5_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k3_xboole_0(esk4_0,esk6_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_95])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_84])])).

cnf(c_0_100,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_30])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(X2,k2_zfmisc_1(esk5_0,esk6_0))) = k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_65])).

cnf(c_0_102,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_104,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_99])).

cnf(c_0_105,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_76,c_0_92])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_65]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_95])).

cnf(c_0_108,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_105,c_0_68])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_110,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_65]),c_0_102])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_107]),c_0_63]),c_0_68]),c_0_108]),c_0_63]),c_0_102])).

cnf(c_0_112,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_111]),c_0_112]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.20/1.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 1.20/1.43  # and selection function GSelectMinInfpos.
% 1.20/1.43  #
% 1.20/1.43  # Preprocessing time       : 0.024 s
% 1.20/1.43  # Presaturation interreduction done
% 1.20/1.43  
% 1.20/1.43  # Proof found!
% 1.20/1.43  # SZS status Theorem
% 1.20/1.43  # SZS output start CNFRefutation
% 1.20/1.43  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 1.20/1.43  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.20/1.43  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 1.20/1.43  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.20/1.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.20/1.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.20/1.43  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 1.20/1.43  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 1.20/1.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.20/1.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.20/1.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.20/1.43  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.20/1.43  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.20/1.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.20/1.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.20/1.43  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.20/1.43  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 1.20/1.43  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.20/1.43  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.20/1.43  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.20/1.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.20/1.43  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.20/1.43  fof(c_0_22, plain, ![X79, X80, X81]:(k2_zfmisc_1(k4_xboole_0(X79,X80),X81)=k4_xboole_0(k2_zfmisc_1(X79,X81),k2_zfmisc_1(X80,X81))&k2_zfmisc_1(X81,k4_xboole_0(X79,X80))=k4_xboole_0(k2_zfmisc_1(X81,X79),k2_zfmisc_1(X81,X80))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 1.20/1.43  fof(c_0_23, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.20/1.43  fof(c_0_24, plain, ![X75, X76, X77, X78]:k2_zfmisc_1(k3_xboole_0(X75,X76),k3_xboole_0(X77,X78))=k3_xboole_0(k2_zfmisc_1(X75,X77),k2_zfmisc_1(X76,X78)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 1.20/1.43  fof(c_0_25, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.20/1.43  fof(c_0_26, plain, ![X65, X66]:k3_tarski(k2_tarski(X65,X66))=k2_xboole_0(X65,X66), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.20/1.43  fof(c_0_27, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.20/1.43  cnf(c_0_28, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.20/1.43  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.20/1.43  cnf(c_0_30, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.20/1.43  cnf(c_0_31, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.20/1.43  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 1.20/1.43  fof(c_0_33, plain, ![X72, X73, X74]:(k2_zfmisc_1(k2_xboole_0(X72,X73),X74)=k2_xboole_0(k2_zfmisc_1(X72,X74),k2_zfmisc_1(X73,X74))&k2_zfmisc_1(X74,k2_xboole_0(X72,X73))=k2_xboole_0(k2_zfmisc_1(X74,X72),k2_zfmisc_1(X74,X73))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 1.20/1.43  cnf(c_0_34, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.20/1.43  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.20/1.43  fof(c_0_36, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.20/1.43  fof(c_0_37, plain, ![X43, X44, X45, X46]:k3_enumset1(X43,X43,X44,X45,X46)=k2_enumset1(X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.20/1.43  fof(c_0_38, plain, ![X47, X48, X49, X50, X51]:k4_enumset1(X47,X47,X48,X49,X50,X51)=k3_enumset1(X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.20/1.43  fof(c_0_39, plain, ![X52, X53, X54, X55, X56, X57]:k5_enumset1(X52,X52,X53,X54,X55,X56,X57)=k4_enumset1(X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.20/1.43  fof(c_0_40, plain, ![X58, X59, X60, X61, X62, X63, X64]:k6_enumset1(X58,X58,X59,X60,X61,X62,X63,X64)=k5_enumset1(X58,X59,X60,X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.20/1.43  fof(c_0_41, plain, ![X67, X68]:((k2_zfmisc_1(X67,X68)!=k1_xboole_0|(X67=k1_xboole_0|X68=k1_xboole_0))&((X67!=k1_xboole_0|k2_zfmisc_1(X67,X68)=k1_xboole_0)&(X68!=k1_xboole_0|k2_zfmisc_1(X67,X68)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.20/1.43  cnf(c_0_42, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 1.20/1.43  cnf(c_0_43, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))=k2_zfmisc_1(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.20/1.43  fof(c_0_44, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k3_xboole_0(X27,X28)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.20/1.43  fof(c_0_45, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 1.20/1.43  cnf(c_0_46, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.20/1.43  cnf(c_0_47, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 1.20/1.43  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.20/1.43  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.20/1.43  cnf(c_0_50, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.20/1.43  cnf(c_0_51, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.20/1.43  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.20/1.43  fof(c_0_53, plain, ![X36, X37]:k2_tarski(X36,X37)=k2_tarski(X37,X36), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.20/1.43  fof(c_0_54, plain, ![X69, X70, X71]:((~r1_tarski(k2_zfmisc_1(X70,X69),k2_zfmisc_1(X71,X69))|X69=k1_xboole_0|r1_tarski(X70,X71))&(~r1_tarski(k2_zfmisc_1(X69,X70),k2_zfmisc_1(X69,X71))|X69=k1_xboole_0|r1_tarski(X70,X71))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 1.20/1.43  cnf(c_0_55, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.20/1.43  cnf(c_0_56, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 1.20/1.43  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.20/1.43  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.20/1.43  cnf(c_0_59, plain, (k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))=k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 1.20/1.43  cnf(c_0_60, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.20/1.43  fof(c_0_61, plain, ![X25, X26]:k2_xboole_0(X25,k3_xboole_0(X25,X26))=X25, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 1.20/1.43  cnf(c_0_62, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.20/1.43  cnf(c_0_63, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 1.20/1.43  cnf(c_0_64, plain, (k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))=k2_zfmisc_1(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_56, c_0_30])).
% 1.20/1.43  cnf(c_0_65, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.20/1.43  cnf(c_0_66, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.20/1.43  cnf(c_0_67, plain, (k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5))))=k2_zfmisc_1(k3_xboole_0(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_xboole_0(X4,X5))))), inference(spm,[status(thm)],[c_0_59, c_0_30])).
% 1.20/1.43  cnf(c_0_68, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_35]), c_0_35]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 1.20/1.43  cnf(c_0_69, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.20/1.43  cnf(c_0_70, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.20/1.43  fof(c_0_71, plain, ![X21, X22]:((k4_xboole_0(X21,X22)!=k1_xboole_0|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|k4_xboole_0(X21,X22)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.20/1.43  cnf(c_0_72, plain, (X1=k1_xboole_0|r1_tarski(X2,k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X2,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.20/1.43  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0)))=k5_xboole_0(k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.20/1.43  cnf(c_0_74, plain, (k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)=k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 1.20/1.43  cnf(c_0_75, negated_conjecture, (k3_tarski(k6_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),X1)))=k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_65]), c_0_68])).
% 1.20/1.43  cnf(c_0_76, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 1.20/1.43  fof(c_0_77, plain, ![X35]:k5_xboole_0(X35,X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 1.20/1.43  fof(c_0_78, plain, ![X30]:r1_tarski(k1_xboole_0,X30), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.20/1.43  cnf(c_0_79, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_29]), c_0_29])).
% 1.20/1.43  cnf(c_0_80, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.20/1.43  cnf(c_0_81, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.20/1.43  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k3_xboole_0(esk3_0,esk5_0),k1_xboole_0)|~r1_tarski(k5_xboole_0(k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,esk4_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.20/1.43  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_76])).
% 1.20/1.43  cnf(c_0_84, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.20/1.43  cnf(c_0_85, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.20/1.43  cnf(c_0_86, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 1.20/1.43  cnf(c_0_87, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_81, c_0_29])).
% 1.20/1.43  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0))=k1_xboole_0|r1_tarski(k3_xboole_0(esk3_0,esk5_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85])])).
% 1.20/1.43  fof(c_0_89, plain, ![X29]:k3_xboole_0(X29,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.20/1.43  cnf(c_0_90, plain, (k5_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3)))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X4)),k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_86, c_0_30])).
% 1.20/1.43  cnf(c_0_91, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk5_0),k1_xboole_0)|r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.20/1.43  cnf(c_0_92, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_89])).
% 1.20/1.43  cnf(c_0_93, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_80]), c_0_86])).
% 1.20/1.43  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)),k3_xboole_0(esk4_0,esk6_0))=k5_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_90, c_0_65])).
% 1.20/1.43  cnf(c_0_95, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|r1_tarski(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_91]), c_0_92])).
% 1.20/1.43  cnf(c_0_96, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)))|k5_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 1.20/1.43  cnf(c_0_97, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k3_xboole_0(esk4_0,esk6_0)=esk4_0), inference(spm,[status(thm)],[c_0_57, c_0_95])).
% 1.20/1.43  cnf(c_0_98, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.20/1.43  cnf(c_0_99, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_84])])).
% 1.20/1.43  cnf(c_0_100, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_30])).
% 1.20/1.43  cnf(c_0_101, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(X2,k2_zfmisc_1(esk5_0,esk6_0)))=k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_65])).
% 1.20/1.43  cnf(c_0_102, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.20/1.43  cnf(c_0_103, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.20/1.43  cnf(c_0_104, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|esk4_0=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_99])).
% 1.20/1.43  cnf(c_0_105, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_76, c_0_92])).
% 1.20/1.43  cnf(c_0_106, negated_conjecture, (k3_xboole_0(X1,X2)=k1_xboole_0|k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_65]), c_0_102])).
% 1.20/1.43  cnf(c_0_107, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_95])).
% 1.20/1.43  cnf(c_0_108, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_105, c_0_68])).
% 1.20/1.43  cnf(c_0_109, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.20/1.43  cnf(c_0_110, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_65]), c_0_102])).
% 1.20/1.43  cnf(c_0_111, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_107]), c_0_63]), c_0_68]), c_0_108]), c_0_63]), c_0_102])).
% 1.20/1.43  cnf(c_0_112, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_109])).
% 1.20/1.43  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_111]), c_0_112]), c_0_63])]), ['proof']).
% 1.20/1.43  # SZS output end CNFRefutation
% 1.20/1.43  # Proof object total steps             : 114
% 1.20/1.43  # Proof object clause steps            : 69
% 1.20/1.43  # Proof object formula steps           : 45
% 1.20/1.43  # Proof object conjectures             : 25
% 1.20/1.43  # Proof object clause conjectures      : 22
% 1.20/1.43  # Proof object formula conjectures     : 3
% 1.20/1.43  # Proof object initial clauses used    : 28
% 1.20/1.43  # Proof object initial formulas used   : 22
% 1.20/1.43  # Proof object generating inferences   : 27
% 1.20/1.43  # Proof object simplifying inferences  : 78
% 1.20/1.43  # Training examples: 0 positive, 0 negative
% 1.20/1.43  # Parsed axioms                        : 29
% 1.20/1.43  # Removed by relevancy pruning/SinE    : 0
% 1.20/1.43  # Initial clauses                      : 39
% 1.20/1.43  # Removed in clause preprocessing      : 8
% 1.20/1.43  # Initial clauses in saturation        : 31
% 1.20/1.43  # Processed clauses                    : 5054
% 1.20/1.43  # ...of these trivial                  : 126
% 1.20/1.43  # ...subsumed                          : 3521
% 1.20/1.43  # ...remaining for further processing  : 1407
% 1.20/1.43  # Other redundant clauses eliminated   : 2
% 1.20/1.43  # Clauses deleted for lack of memory   : 0
% 1.20/1.43  # Backward-subsumed                    : 36
% 1.20/1.43  # Backward-rewritten                   : 972
% 1.20/1.43  # Generated clauses                    : 80694
% 1.20/1.43  # ...of the previous two non-trivial   : 74362
% 1.20/1.43  # Contextual simplify-reflections      : 1
% 1.20/1.43  # Paramodulations                      : 80692
% 1.20/1.43  # Factorizations                       : 0
% 1.20/1.43  # Equation resolutions                 : 2
% 1.20/1.43  # Propositional unsat checks           : 0
% 1.20/1.43  #    Propositional check models        : 0
% 1.20/1.43  #    Propositional check unsatisfiable : 0
% 1.20/1.43  #    Propositional clauses             : 0
% 1.20/1.43  #    Propositional clauses after purity: 0
% 1.20/1.43  #    Propositional unsat core size     : 0
% 1.20/1.43  #    Propositional preprocessing time  : 0.000
% 1.20/1.43  #    Propositional encoding time       : 0.000
% 1.20/1.43  #    Propositional solver time         : 0.000
% 1.20/1.43  #    Success case prop preproc time    : 0.000
% 1.20/1.43  #    Success case prop encoding time   : 0.000
% 1.20/1.43  #    Success case prop solver time     : 0.000
% 1.20/1.43  # Current number of processed clauses  : 366
% 1.20/1.43  #    Positive orientable unit clauses  : 104
% 1.20/1.43  #    Positive unorientable unit clauses: 11
% 1.20/1.43  #    Negative unit clauses             : 1
% 1.20/1.43  #    Non-unit-clauses                  : 250
% 1.20/1.43  # Current number of unprocessed clauses: 68829
% 1.20/1.43  # ...number of literals in the above   : 155983
% 1.20/1.43  # Current number of archived formulas  : 0
% 1.20/1.43  # Current number of archived clauses   : 1047
% 1.20/1.43  # Clause-clause subsumption calls (NU) : 70445
% 1.20/1.43  # Rec. Clause-clause subsumption calls : 67524
% 1.20/1.43  # Non-unit clause-clause subsumptions  : 3469
% 1.20/1.43  # Unit Clause-clause subsumption calls : 452
% 1.20/1.43  # Rewrite failures with RHS unbound    : 0
% 1.20/1.43  # BW rewrite match attempts            : 748
% 1.20/1.43  # BW rewrite match successes           : 185
% 1.20/1.43  # Condensation attempts                : 0
% 1.20/1.43  # Condensation successes               : 0
% 1.20/1.43  # Termbank termtop insertions          : 2587232
% 1.20/1.44  
% 1.20/1.44  # -------------------------------------------------
% 1.20/1.44  # User time                : 1.049 s
% 1.20/1.44  # System time              : 0.048 s
% 1.20/1.44  # Total time               : 1.097 s
% 1.20/1.44  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
