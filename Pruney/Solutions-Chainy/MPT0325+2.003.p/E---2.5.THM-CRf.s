%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:06 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  127 (18762 expanded)
%              Number of clauses        :   88 (8931 expanded)
%              Number of leaves         :   19 (4730 expanded)
%              Depth                    :   27
%              Number of atoms          :  183 (34588 expanded)
%              Number of equality atoms :  153 (29766 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X67,X68,X69,X70] : k2_zfmisc_1(k3_xboole_0(X67,X68),k3_xboole_0(X69,X70)) = k3_xboole_0(k2_zfmisc_1(X67,X69),k2_zfmisc_1(X68,X70)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X62,X63] :
      ( ( k2_zfmisc_1(X62,X63) != k1_xboole_0
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0 )
      & ( X62 != k1_xboole_0
        | k2_zfmisc_1(X62,X63) = k1_xboole_0 )
      & ( X63 != k1_xboole_0
        | k2_zfmisc_1(X62,X63) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X14] : k3_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X71,X72,X73] :
      ( k2_zfmisc_1(k4_xboole_0(X71,X72),X73) = k4_xboole_0(k2_zfmisc_1(X71,X73),k2_zfmisc_1(X72,X73))
      & k2_zfmisc_1(X73,k4_xboole_0(X71,X72)) = k4_xboole_0(k2_zfmisc_1(X73,X71),k2_zfmisc_1(X73,X72)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_33,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),X1),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),X2)) = k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),X1),k1_xboole_0) = k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

fof(c_0_47,plain,(
    ! [X30] : k5_xboole_0(X30,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_xboole_0(esk3_0,k1_xboole_0),esk4_0),X1) = k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_34]),c_0_28]),c_0_44])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,k1_xboole_0),X2) = k2_zfmisc_1(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_42])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X22,X23] :
      ( ( k4_xboole_0(X22,X23) != k1_xboole_0
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | k4_xboole_0(X22,X23) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,k1_xboole_0),esk4_0) = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_27]),c_0_37]),c_0_42]),c_0_51]),c_0_52]),c_0_51])).

fof(c_0_57,plain,(
    ! [X60,X61] : k3_tarski(k2_tarski(X60,X61)) = k2_xboole_0(X60,X61) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(X2,k2_zfmisc_1(esk5_0,esk6_0))) = k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0)) = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_63,plain,(
    ! [X64,X65,X66] :
      ( k2_zfmisc_1(k2_xboole_0(X64,X65),X66) = k2_xboole_0(k2_zfmisc_1(X64,X66),k2_zfmisc_1(X65,X66))
      & k2_zfmisc_1(X66,k2_xboole_0(X64,X65)) = k2_xboole_0(k2_zfmisc_1(X66,X64),k2_zfmisc_1(X66,X65)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_64,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_67,plain,(
    ! [X38,X39,X40,X41] : k3_enumset1(X38,X38,X39,X40,X41) = k2_enumset1(X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_68,plain,(
    ! [X42,X43,X44,X45,X46] : k4_enumset1(X42,X42,X43,X44,X45,X46) = k3_enumset1(X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_69,plain,(
    ! [X47,X48,X49,X50,X51,X52] : k5_enumset1(X47,X47,X48,X49,X50,X51,X52) = k4_enumset1(X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_70,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59] : k6_enumset1(X53,X53,X54,X55,X56,X57,X58,X59) = k5_enumset1(X53,X54,X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_59]),c_0_28]),c_0_44])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0)) = k1_xboole_0
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_35])])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_76,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_81,plain,(
    ! [X31,X32] : k2_tarski(X31,X32) = k2_tarski(X32,X31) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75]),c_0_76]),c_0_76]),c_0_77]),c_0_77]),c_0_78]),c_0_78]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

cnf(c_0_86,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_87,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k3_xboole_0(X26,X27)) = X26 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_51]),c_0_42]),c_0_51])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_84])).

cnf(c_0_90,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_91,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5)))) = k2_zfmisc_1(k3_xboole_0(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_xboole_0(X4,X5)))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_27])).

cnf(c_0_92,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_65]),c_0_65]),c_0_76]),c_0_76]),c_0_77]),c_0_77]),c_0_78]),c_0_78]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_35])])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_75]),c_0_75]),c_0_76]),c_0_76]),c_0_77]),c_0_77]),c_0_78]),c_0_78]),c_0_79]),c_0_79]),c_0_80]),c_0_80])).

cnf(c_0_97,negated_conjecture,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),X1))) = k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_28]),c_0_92])).

cnf(c_0_98,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_75]),c_0_76]),c_0_77]),c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_40]),c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0) = k2_zfmisc_1(X1,k5_xboole_0(X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_95]),c_0_35])).

cnf(c_0_101,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_98])).

cnf(c_0_102,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[c_0_99,c_0_36])).

cnf(c_0_103,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk4_0,k1_xboole_0)) = k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)),k5_xboole_0(esk4_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_52])).

cnf(c_0_105,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X2) = k2_zfmisc_1(X1,k5_xboole_0(X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_95]),c_0_37]),c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)) = k1_xboole_0
    | k5_xboole_0(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_104])).

cnf(c_0_107,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X5,X3))) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X4,X5),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_27])).

cnf(c_0_108,negated_conjecture,
    ( k5_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_105]),c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0)) = k3_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_28])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | k5_xboole_0(X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_95])).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_35]),c_0_35])])).

cnf(c_0_113,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk6_0)) = k2_zfmisc_1(esk3_0,k3_xboole_0(k3_xboole_0(esk4_0,esk6_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0)
    | r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k3_xboole_0(k3_xboole_0(esk4_0,esk6_0),esk4_0)))) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_113]),c_0_85])).

cnf(c_0_116,negated_conjecture,
    ( k1_xboole_0 = X1
    | r1_tarski(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_114]),c_0_95])).

cnf(c_0_117,plain,
    ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) = k2_zfmisc_1(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_27])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_44])).

cnf(c_0_119,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_28])).

cnf(c_0_120,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_101]),c_0_52]),c_0_120])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0)) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_121])).

cnf(c_0_123,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_118])])).

cnf(c_0_124,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_28]),c_0_44])).

cnf(c_0_125,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_122]),c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125]),c_0_37]),c_0_125]),c_0_37]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:45:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.46/0.63  # and selection function GSelectMinInfpos.
% 0.46/0.63  #
% 0.46/0.63  # Preprocessing time       : 0.027 s
% 0.46/0.63  # Presaturation interreduction done
% 0.46/0.63  
% 0.46/0.63  # Proof found!
% 0.46/0.63  # SZS status Theorem
% 0.46/0.63  # SZS output start CNFRefutation
% 0.46/0.63  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.46/0.63  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.46/0.63  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.46/0.63  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.46/0.63  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.46/0.63  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 0.46/0.63  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.46/0.63  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.46/0.63  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.46/0.63  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.46/0.63  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.46/0.63  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.46/0.63  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.46/0.63  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.46/0.63  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.46/0.63  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.46/0.63  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.46/0.63  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.46/0.63  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.46/0.63  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.46/0.63  fof(c_0_20, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.46/0.63  fof(c_0_21, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.46/0.63  fof(c_0_22, plain, ![X67, X68, X69, X70]:k2_zfmisc_1(k3_xboole_0(X67,X68),k3_xboole_0(X69,X70))=k3_xboole_0(k2_zfmisc_1(X67,X69),k2_zfmisc_1(X68,X70)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.46/0.63  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.63  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.63  fof(c_0_25, plain, ![X62, X63]:((k2_zfmisc_1(X62,X63)!=k1_xboole_0|(X62=k1_xboole_0|X63=k1_xboole_0))&((X62!=k1_xboole_0|k2_zfmisc_1(X62,X63)=k1_xboole_0)&(X63!=k1_xboole_0|k2_zfmisc_1(X62,X63)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.46/0.63  fof(c_0_26, plain, ![X14]:k3_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.46/0.63  cnf(c_0_27, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.46/0.63  cnf(c_0_28, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.46/0.63  cnf(c_0_29, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.46/0.63  cnf(c_0_30, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.46/0.63  cnf(c_0_31, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.46/0.63  fof(c_0_32, plain, ![X71, X72, X73]:(k2_zfmisc_1(k4_xboole_0(X71,X72),X73)=k4_xboole_0(k2_zfmisc_1(X71,X73),k2_zfmisc_1(X72,X73))&k2_zfmisc_1(X73,k4_xboole_0(X71,X72))=k4_xboole_0(k2_zfmisc_1(X73,X71),k2_zfmisc_1(X73,X72))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 0.46/0.63  fof(c_0_33, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.46/0.63  cnf(c_0_34, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),X1),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),X2))=k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.46/0.63  cnf(c_0_35, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 0.46/0.63  cnf(c_0_36, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.46/0.63  cnf(c_0_37, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_31])).
% 0.46/0.63  cnf(c_0_38, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.46/0.63  cnf(c_0_39, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.46/0.63  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.63  cnf(c_0_41, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),X1),k1_xboole_0)=k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.46/0.63  cnf(c_0_42, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0)=k2_zfmisc_1(k3_xboole_0(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.46/0.63  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_27])).
% 0.46/0.63  cnf(c_0_44, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.63  cnf(c_0_45, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_40])).
% 0.46/0.63  cnf(c_0_46, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))=k2_zfmisc_1(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.46/0.63  fof(c_0_47, plain, ![X30]:k5_xboole_0(X30,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.46/0.63  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k3_xboole_0(esk3_0,k1_xboole_0),esk4_0),X1)=k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 0.46/0.63  cnf(c_0_49, negated_conjecture, (k3_xboole_0(X1,X2)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,X2))!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_34]), c_0_28]), c_0_44])).
% 0.46/0.63  cnf(c_0_50, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.46/0.63  cnf(c_0_51, plain, (k2_zfmisc_1(k3_xboole_0(X1,k1_xboole_0),X2)=k2_zfmisc_1(X1,k3_xboole_0(X2,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_42])).
% 0.46/0.63  cnf(c_0_52, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.46/0.63  fof(c_0_53, plain, ![X22, X23]:((k4_xboole_0(X22,X23)!=k1_xboole_0|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|k4_xboole_0(X22,X23)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.46/0.63  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,k1_xboole_0),esk4_0)=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_48])).
% 0.46/0.63  cnf(c_0_55, negated_conjecture, (X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_30])).
% 0.46/0.63  cnf(c_0_56, plain, (k2_zfmisc_1(X1,k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_27]), c_0_37]), c_0_42]), c_0_51]), c_0_52]), c_0_51])).
% 0.46/0.63  fof(c_0_57, plain, ![X60, X61]:k3_tarski(k2_tarski(X60,X61))=k2_xboole_0(X60,X61), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.46/0.63  fof(c_0_58, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.46/0.63  cnf(c_0_59, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(X2,k2_zfmisc_1(esk5_0,esk6_0)))=k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.46/0.63  cnf(c_0_60, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.46/0.63  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0))=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k3_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_51])).
% 0.46/0.63  cnf(c_0_62, negated_conjecture, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.46/0.63  fof(c_0_63, plain, ![X64, X65, X66]:(k2_zfmisc_1(k2_xboole_0(X64,X65),X66)=k2_xboole_0(k2_zfmisc_1(X64,X66),k2_zfmisc_1(X65,X66))&k2_zfmisc_1(X66,k2_xboole_0(X64,X65))=k2_xboole_0(k2_zfmisc_1(X66,X64),k2_zfmisc_1(X66,X65))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.46/0.63  cnf(c_0_64, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.46/0.63  cnf(c_0_65, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.46/0.63  fof(c_0_66, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.46/0.63  fof(c_0_67, plain, ![X38, X39, X40, X41]:k3_enumset1(X38,X38,X39,X40,X41)=k2_enumset1(X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.46/0.63  fof(c_0_68, plain, ![X42, X43, X44, X45, X46]:k4_enumset1(X42,X42,X43,X44,X45,X46)=k3_enumset1(X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.46/0.63  fof(c_0_69, plain, ![X47, X48, X49, X50, X51, X52]:k5_enumset1(X47,X47,X48,X49,X50,X51,X52)=k4_enumset1(X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.46/0.63  fof(c_0_70, plain, ![X53, X54, X55, X56, X57, X58, X59]:k6_enumset1(X53,X53,X54,X55,X56,X57,X58,X59)=k5_enumset1(X53,X54,X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.46/0.63  cnf(c_0_71, negated_conjecture, (k3_xboole_0(X1,X2)=k1_xboole_0|k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_59]), c_0_28]), c_0_44])).
% 0.46/0.63  cnf(c_0_72, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_60, c_0_40])).
% 0.46/0.63  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0))=k1_xboole_0|k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_35])])).
% 0.46/0.63  cnf(c_0_74, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.46/0.63  cnf(c_0_75, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.46/0.63  cnf(c_0_76, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.46/0.63  cnf(c_0_77, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.46/0.63  cnf(c_0_78, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.46/0.63  cnf(c_0_79, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.46/0.63  cnf(c_0_80, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.46/0.63  fof(c_0_81, plain, ![X31, X32]:k2_tarski(X31,X32)=k2_tarski(X32,X31), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.46/0.63  cnf(c_0_82, negated_conjecture, (X1=k1_xboole_0|k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_30])).
% 0.46/0.63  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.63  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0))=k1_xboole_0|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.46/0.63  cnf(c_0_85, plain, (k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))=k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75]), c_0_76]), c_0_76]), c_0_77]), c_0_77]), c_0_78]), c_0_78]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.46/0.63  cnf(c_0_86, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.46/0.63  fof(c_0_87, plain, ![X26, X27]:k2_xboole_0(X26,k3_xboole_0(X26,X27))=X26, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.46/0.63  cnf(c_0_88, negated_conjecture, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0|k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_51]), c_0_42]), c_0_51])).
% 0.46/0.63  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k1_xboole_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_84])).
% 0.46/0.63  cnf(c_0_90, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.46/0.63  cnf(c_0_91, plain, (k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5))))=k2_zfmisc_1(k3_xboole_0(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_xboole_0(X4,X5))))), inference(spm,[status(thm)],[c_0_85, c_0_27])).
% 0.46/0.63  cnf(c_0_92, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_65]), c_0_65]), c_0_76]), c_0_76]), c_0_77]), c_0_77]), c_0_78]), c_0_78]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.46/0.63  cnf(c_0_93, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.46/0.63  cnf(c_0_94, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.46/0.63  cnf(c_0_95, negated_conjecture, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_35])])).
% 0.46/0.63  cnf(c_0_96, plain, (k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)=k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_75]), c_0_75]), c_0_76]), c_0_76]), c_0_77]), c_0_77]), c_0_78]), c_0_78]), c_0_79]), c_0_79]), c_0_80]), c_0_80])).
% 0.46/0.63  cnf(c_0_97, negated_conjecture, (k3_tarski(k6_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),X1)))=k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_28]), c_0_92])).
% 0.46/0.63  cnf(c_0_98, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_75]), c_0_76]), c_0_77]), c_0_78]), c_0_79]), c_0_80])).
% 0.46/0.63  cnf(c_0_99, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_40]), c_0_40])).
% 0.46/0.63  cnf(c_0_100, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0)=k2_zfmisc_1(X1,k5_xboole_0(X2,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_95]), c_0_35])).
% 0.46/0.63  cnf(c_0_101, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_98])).
% 0.46/0.63  cnf(c_0_102, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[c_0_99, c_0_36])).
% 0.46/0.63  cnf(c_0_103, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk4_0,k1_xboole_0))=k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_100])).
% 0.46/0.63  cnf(c_0_104, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)),k5_xboole_0(esk4_0,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_52])).
% 0.46/0.63  cnf(c_0_105, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(X1,k1_xboole_0),X2)=k2_zfmisc_1(X1,k5_xboole_0(X2,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_95]), c_0_37]), c_0_100])).
% 0.46/0.63  cnf(c_0_106, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))=k1_xboole_0|k5_xboole_0(esk4_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_104])).
% 0.46/0.63  cnf(c_0_107, plain, (k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X5,X3)))=k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X4,X5),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27]), c_0_27])).
% 0.46/0.63  cnf(c_0_108, negated_conjecture, (k5_xboole_0(X1,k1_xboole_0)=k1_xboole_0|k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_105]), c_0_100])).
% 0.46/0.63  cnf(c_0_109, negated_conjecture, (k5_xboole_0(esk4_0,k1_xboole_0)=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_106])).
% 0.46/0.63  cnf(c_0_110, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))=k3_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_107, c_0_28])).
% 0.46/0.63  cnf(c_0_111, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|k5_xboole_0(X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_95])).
% 0.46/0.63  cnf(c_0_112, negated_conjecture, (k5_xboole_0(X1,k1_xboole_0)=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_35]), c_0_35])])).
% 0.46/0.63  cnf(c_0_113, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk6_0))=k2_zfmisc_1(esk3_0,k3_xboole_0(k3_xboole_0(esk4_0,esk6_0),esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_110])).
% 0.46/0.63  cnf(c_0_114, negated_conjecture, (r1_tarski(esk3_0,esk5_0)|r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 0.46/0.63  cnf(c_0_115, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k3_xboole_0(k3_xboole_0(esk4_0,esk6_0),esk4_0))))=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_113]), c_0_85])).
% 0.46/0.63  cnf(c_0_116, negated_conjecture, (k1_xboole_0=X1|r1_tarski(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_114]), c_0_95])).
% 0.46/0.63  cnf(c_0_117, plain, (k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))=k2_zfmisc_1(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_50, c_0_27])).
% 0.46/0.63  cnf(c_0_118, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_44])).
% 0.46/0.63  cnf(c_0_119, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0)))=k5_xboole_0(k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_117, c_0_28])).
% 0.46/0.63  cnf(c_0_120, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_118])).
% 0.46/0.63  cnf(c_0_121, negated_conjecture, (k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_101]), c_0_52]), c_0_120])).
% 0.46/0.63  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk6_0))=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_121])).
% 0.46/0.63  cnf(c_0_123, negated_conjecture, (~r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_118])])).
% 0.46/0.63  cnf(c_0_124, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_28]), c_0_44])).
% 0.46/0.63  cnf(c_0_125, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_122]), c_0_123])).
% 0.46/0.63  cnf(c_0_126, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125]), c_0_37]), c_0_125]), c_0_37]), c_0_37])]), ['proof']).
% 0.46/0.63  # SZS output end CNFRefutation
% 0.46/0.63  # Proof object total steps             : 127
% 0.46/0.63  # Proof object clause steps            : 88
% 0.46/0.63  # Proof object formula steps           : 39
% 0.46/0.63  # Proof object conjectures             : 48
% 0.46/0.63  # Proof object clause conjectures      : 45
% 0.46/0.63  # Proof object formula conjectures     : 3
% 0.46/0.63  # Proof object initial clauses used    : 25
% 0.46/0.63  # Proof object initial formulas used   : 19
% 0.46/0.63  # Proof object generating inferences   : 45
% 0.46/0.63  # Proof object simplifying inferences  : 103
% 0.46/0.63  # Training examples: 0 positive, 0 negative
% 0.46/0.63  # Parsed axioms                        : 24
% 0.46/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.63  # Initial clauses                      : 35
% 0.46/0.63  # Removed in clause preprocessing      : 8
% 0.46/0.63  # Initial clauses in saturation        : 27
% 0.46/0.63  # Processed clauses                    : 1966
% 0.46/0.63  # ...of these trivial                  : 120
% 0.46/0.63  # ...subsumed                          : 1207
% 0.46/0.63  # ...remaining for further processing  : 639
% 0.46/0.63  # Other redundant clauses eliminated   : 8
% 0.46/0.63  # Clauses deleted for lack of memory   : 0
% 0.46/0.63  # Backward-subsumed                    : 77
% 0.46/0.63  # Backward-rewritten                   : 395
% 0.46/0.63  # Generated clauses                    : 18765
% 0.46/0.63  # ...of the previous two non-trivial   : 15496
% 0.46/0.63  # Contextual simplify-reflections      : 1
% 0.46/0.63  # Paramodulations                      : 18742
% 0.46/0.63  # Factorizations                       : 15
% 0.46/0.63  # Equation resolutions                 : 8
% 0.46/0.63  # Propositional unsat checks           : 0
% 0.46/0.63  #    Propositional check models        : 0
% 0.46/0.63  #    Propositional check unsatisfiable : 0
% 0.46/0.63  #    Propositional clauses             : 0
% 0.46/0.63  #    Propositional clauses after purity: 0
% 0.46/0.63  #    Propositional unsat core size     : 0
% 0.46/0.63  #    Propositional preprocessing time  : 0.000
% 0.46/0.63  #    Propositional encoding time       : 0.000
% 0.46/0.63  #    Propositional solver time         : 0.000
% 0.46/0.63  #    Success case prop preproc time    : 0.000
% 0.46/0.63  #    Success case prop encoding time   : 0.000
% 0.46/0.63  #    Success case prop solver time     : 0.000
% 0.46/0.63  # Current number of processed clauses  : 138
% 0.46/0.63  #    Positive orientable unit clauses  : 53
% 0.46/0.63  #    Positive unorientable unit clauses: 1
% 0.46/0.63  #    Negative unit clauses             : 2
% 0.46/0.63  #    Non-unit-clauses                  : 82
% 0.46/0.63  # Current number of unprocessed clauses: 9259
% 0.46/0.63  # ...number of literals in the above   : 17406
% 0.46/0.63  # Current number of archived formulas  : 0
% 0.46/0.63  # Current number of archived clauses   : 507
% 0.46/0.63  # Clause-clause subsumption calls (NU) : 7342
% 0.46/0.63  # Rec. Clause-clause subsumption calls : 6706
% 0.46/0.63  # Non-unit clause-clause subsumptions  : 531
% 0.46/0.63  # Unit Clause-clause subsumption calls : 569
% 0.46/0.63  # Rewrite failures with RHS unbound    : 0
% 0.46/0.63  # BW rewrite match attempts            : 431
% 0.46/0.63  # BW rewrite match successes           : 121
% 0.46/0.63  # Condensation attempts                : 0
% 0.46/0.63  # Condensation successes               : 0
% 0.46/0.63  # Termbank termtop insertions          : 426492
% 0.46/0.63  
% 0.46/0.63  # -------------------------------------------------
% 0.46/0.63  # User time                : 0.281 s
% 0.46/0.63  # System time              : 0.014 s
% 0.46/0.63  # Total time               : 0.295 s
% 0.46/0.63  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
