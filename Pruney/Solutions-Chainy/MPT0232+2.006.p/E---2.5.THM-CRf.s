%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 341 expanded)
%              Number of clauses        :   45 ( 141 expanded)
%              Number of leaves         :   20 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 425 expanded)
%              Number of equality atoms :   69 ( 315 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t27_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => k2_tarski(X1,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t95_enumset1,axiom,(
    ! [X1,X2] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(l20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k2_xboole_0(X24,X25) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_21,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
       => k2_tarski(X1,X2) = k1_tarski(X3) ) ),
    inference(assume_negation,[status(cth)],[t27_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X72,X73,X74,X75,X76] : k3_enumset1(X72,X73,X74,X75,X76) = k2_xboole_0(k2_enumset1(X72,X73,X74,X75),k1_tarski(X76)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_24,plain,(
    ! [X91] : k2_tarski(X91,X91) = k1_tarski(X91) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X92,X93] : k2_enumset1(X92,X92,X92,X93) = k2_tarski(X92,X93) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(X17,k2_xboole_0(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0))
    & k2_tarski(esk2_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_30,plain,(
    ! [X77,X78,X79,X80,X81,X82] : k4_enumset1(X77,X78,X79,X80,X81,X82) = k2_xboole_0(k1_tarski(X77),k3_enumset1(X78,X79,X80,X81,X82)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X83,X84,X85,X86,X87,X88,X89,X90] : k6_enumset1(X83,X84,X85,X86,X87,X88,X89,X90) = k2_xboole_0(k2_tarski(X83,X84),k4_enumset1(X85,X86,X87,X88,X89,X90)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_32]),c_0_33]),c_0_33])).

fof(c_0_42,plain,(
    ! [X61,X62] : r1_tarski(X61,k2_xboole_0(X61,X62)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_43,plain,(
    ! [X63,X64] : k2_tarski(X63,X64) = k2_xboole_0(k1_tarski(X63),k1_tarski(X64)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_44,plain,(
    ! [X97,X98] : k6_enumset1(X97,X97,X97,X97,X97,X97,X97,X98) = k2_tarski(X97,X98) ),
    inference(variable_rename,[status(thm)],[t95_enumset1])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_32]),c_0_33]),c_0_39])).

fof(c_0_47,plain,(
    ! [X103,X104] :
      ( ( ~ r1_tarski(X103,k1_tarski(X104))
        | X103 = k1_xboole_0
        | X103 = k1_tarski(X104) )
      & ( X103 != k1_xboole_0
        | r1_tarski(X103,k1_tarski(X104)) )
      & ( X103 != k1_tarski(X104)
        | r1_tarski(X103,k1_tarski(X104)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),X1)
    | ~ r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X8,X8,X8,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_33]),c_0_46])).

fof(c_0_53,plain,(
    ! [X59,X60] : k2_xboole_0(X59,k2_xboole_0(X59,X60)) = k2_xboole_0(X59,X60) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),k2_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_33]),c_0_52])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_32]),c_0_33]),c_0_33])).

fof(c_0_63,plain,(
    ! [X101,X102] :
      ( ( k4_xboole_0(k1_tarski(X101),X102) != k1_tarski(X101)
        | ~ r2_hidden(X101,X102) )
      & ( r2_hidden(X101,X102)
        | k4_xboole_0(k1_tarski(X101),X102) = k1_tarski(X101) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_56]),c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

fof(c_0_66,plain,(
    ! [X44] : r1_tarski(k1_xboole_0,X44) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_67,plain,(
    ! [X52] :
      ( ~ r1_tarski(X52,k1_xboole_0)
      | X52 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_68,plain,(
    ! [X48,X49] : r1_tarski(k4_xboole_0(X48,X49),X48) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_69,plain,(
    ! [X99,X100] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X99),X100),X100)
      | r2_hidden(X99,X100) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_28])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) != k2_enumset1(X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_77,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_71]),c_0_72])])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_79,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_32]),c_0_33])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_77]),c_0_81])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_59]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:45:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.39  fof(t27_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>k2_tarski(X1,X2)=k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 0.20/0.39  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.20/0.39  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.39  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.20/0.39  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.20/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.39  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.39  fof(t95_enumset1, axiom, ![X1, X2]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_enumset1)).
% 0.20/0.39  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.39  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.20/0.39  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.39  fof(l20_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(c_0_20, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k2_xboole_0(X24,X25)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.39  fof(c_0_21, plain, ![X9, X10]:k2_xboole_0(X9,X10)=k2_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.39  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>k2_tarski(X1,X2)=k1_tarski(X3))), inference(assume_negation,[status(cth)],[t27_zfmisc_1])).
% 0.20/0.39  fof(c_0_23, plain, ![X72, X73, X74, X75, X76]:k3_enumset1(X72,X73,X74,X75,X76)=k2_xboole_0(k2_enumset1(X72,X73,X74,X75),k1_tarski(X76)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.20/0.39  fof(c_0_24, plain, ![X91]:k2_tarski(X91,X91)=k1_tarski(X91), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  fof(c_0_25, plain, ![X92, X93]:k2_enumset1(X92,X92,X92,X93)=k2_tarski(X92,X93), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.20/0.39  fof(c_0_26, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|r1_tarski(X17,k2_xboole_0(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.39  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  fof(c_0_29, negated_conjecture, (r1_tarski(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0))&k2_tarski(esk2_0,esk3_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.20/0.39  fof(c_0_30, plain, ![X77, X78, X79, X80, X81, X82]:k4_enumset1(X77,X78,X79,X80,X81,X82)=k2_xboole_0(k1_tarski(X77),k3_enumset1(X78,X79,X80,X81,X82)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.20/0.39  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_tarski(esk2_0,esk3_0),k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  fof(c_0_37, plain, ![X83, X84, X85, X86, X87, X88, X89, X90]:k6_enumset1(X83,X84,X85,X86,X87,X88,X89,X90)=k2_xboole_0(k2_tarski(X83,X84),k4_enumset1(X85,X86,X87,X88,X89,X90)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.20/0.39  cnf(c_0_38, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_39, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.39  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_32]), c_0_33]), c_0_33])).
% 0.20/0.39  fof(c_0_42, plain, ![X61, X62]:r1_tarski(X61,k2_xboole_0(X61,X62)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.39  fof(c_0_43, plain, ![X63, X64]:k2_tarski(X63,X64)=k2_xboole_0(k1_tarski(X63),k1_tarski(X64)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.39  fof(c_0_44, plain, ![X97, X98]:k6_enumset1(X97,X97,X97,X97,X97,X97,X97,X98)=k2_tarski(X97,X98), inference(variable_rename,[status(thm)],[t95_enumset1])).
% 0.20/0.39  cnf(c_0_45, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_46, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_enumset1(X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_32]), c_0_33]), c_0_39])).
% 0.20/0.39  fof(c_0_47, plain, ![X103, X104]:((~r1_tarski(X103,k1_tarski(X104))|(X103=k1_xboole_0|X103=k1_tarski(X104)))&((X103!=k1_xboole_0|r1_tarski(X103,k1_tarski(X104)))&(X103!=k1_tarski(X104)|r1_tarski(X103,k1_tarski(X104))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),X1)|~r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.39  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_52, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X8,X8,X8,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_33]), c_0_46])).
% 0.20/0.39  fof(c_0_53, plain, ![X59, X60]:k2_xboole_0(X59,k2_xboole_0(X59,X60))=k2_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.20/0.39  cnf(c_0_54, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),k2_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.39  cnf(c_0_56, plain, (k2_enumset1(X1,X1,X1,X2)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (k2_tarski(esk2_0,esk3_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_58, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))))=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_33]), c_0_52])).
% 0.20/0.39  cnf(c_0_59, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.39  cnf(c_0_60, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_32]), c_0_33]), c_0_33])).
% 0.20/0.39  fof(c_0_63, plain, ![X101, X102]:((k4_xboole_0(k1_tarski(X101),X102)!=k1_tarski(X101)|~r2_hidden(X101,X102))&(r2_hidden(X101,X102)|k4_xboole_0(k1_tarski(X101),X102)=k1_tarski(X101))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_64, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_56]), c_0_59])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.20/0.39  fof(c_0_66, plain, ![X44]:r1_tarski(k1_xboole_0,X44), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  fof(c_0_67, plain, ![X52]:(~r1_tarski(X52,k1_xboole_0)|X52=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.39  fof(c_0_68, plain, ![X48, X49]:r1_tarski(k4_xboole_0(X48,X49),X48), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.39  fof(c_0_69, plain, ![X99, X100]:(~r1_tarski(k2_xboole_0(k1_tarski(X99),X100),X100)|r2_hidden(X99,X100)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).
% 0.20/0.39  cnf(c_0_70, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_28])).
% 0.20/0.39  cnf(c_0_72, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.39  cnf(c_0_73, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_74, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.39  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.39  cnf(c_0_76, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)!=k2_enumset1(X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_71]), c_0_72])])).
% 0.20/0.39  cnf(c_0_78, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.39  fof(c_0_79, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_80, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_32]), c_0_33])).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.20/0.39  cnf(c_0_82, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_77]), c_0_81])).
% 0.20/0.39  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_82])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_59]), c_0_84])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 86
% 0.20/0.39  # Proof object clause steps            : 45
% 0.20/0.39  # Proof object formula steps           : 41
% 0.20/0.39  # Proof object conjectures             : 16
% 0.20/0.39  # Proof object clause conjectures      : 13
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 21
% 0.20/0.39  # Proof object initial formulas used   : 20
% 0.20/0.39  # Proof object generating inferences   : 12
% 0.20/0.39  # Proof object simplifying inferences  : 42
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 37
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 46
% 0.20/0.39  # Removed in clause preprocessing      : 6
% 0.20/0.39  # Initial clauses in saturation        : 40
% 0.20/0.39  # Processed clauses                    : 144
% 0.20/0.39  # ...of these trivial                  : 5
% 0.20/0.39  # ...subsumed                          : 30
% 0.20/0.39  # ...remaining for further processing  : 109
% 0.20/0.39  # Other redundant clauses eliminated   : 4
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 3
% 0.20/0.39  # Backward-rewritten                   : 12
% 0.20/0.39  # Generated clauses                    : 356
% 0.20/0.39  # ...of the previous two non-trivial   : 276
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 352
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 4
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 54
% 0.20/0.39  #    Positive orientable unit clauses  : 17
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 5
% 0.20/0.39  #    Non-unit-clauses                  : 31
% 0.20/0.39  # Current number of unprocessed clauses: 204
% 0.20/0.39  # ...number of literals in the above   : 432
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 57
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 241
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 198
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 27
% 0.20/0.39  # Unit Clause-clause subsumption calls : 8
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 25
% 0.20/0.39  # BW rewrite match successes           : 15
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 6031
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.037 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.040 s
% 0.20/0.39  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
