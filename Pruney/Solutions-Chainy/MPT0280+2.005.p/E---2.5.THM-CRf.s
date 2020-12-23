%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:09 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 271 expanded)
%              Number of clauses        :   39 ( 110 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 318 expanded)
%              Number of equality atoms :   40 ( 227 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t110_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t81_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X58,X59] : k3_tarski(k2_tarski(X58,X59)) = k2_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X36,X37,X38,X39] : k3_enumset1(X36,X36,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X40,X41,X42,X43,X44] : k4_enumset1(X40,X40,X41,X42,X43,X44) = k3_enumset1(X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X45,X46,X47,X48,X49,X50] : k5_enumset1(X45,X45,X46,X47,X48,X49,X50) = k4_enumset1(X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57) = k5_enumset1(X51,X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,plain,(
    ! [X29,X30] : k2_xboole_0(X29,X30) = k5_xboole_0(X29,k4_xboole_0(X30,X29)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_31,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_32,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,k3_xboole_0(X23,X24))
      | r1_tarski(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_33,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k3_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_47,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_35]),c_0_42]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

fof(c_0_48,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X18)
      | r1_tarski(k5_xboole_0(X17,X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_51,plain,(
    ! [X20,X21] : r1_tarski(k3_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(esk1_0),k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_44]),c_0_47]),c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k5_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_56,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))
    | ~ r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_59,plain,(
    ! [X60,X61] :
      ( ~ r1_tarski(X60,X61)
      | r1_tarski(k1_zfmisc_1(X60),k1_zfmisc_1(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_61,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | r1_tarski(X14,k2_xboole_0(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))
    | ~ r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_53]),c_0_58])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))
    | ~ r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_47])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

fof(c_0_69,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_44])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_47])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_44])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.99/1.19  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.99/1.19  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.99/1.19  #
% 0.99/1.19  # Preprocessing time       : 0.028 s
% 0.99/1.19  # Presaturation interreduction done
% 0.99/1.19  
% 0.99/1.19  # Proof found!
% 0.99/1.19  # SZS status Theorem
% 0.99/1.19  # SZS output start CNFRefutation
% 0.99/1.19  fof(t81_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 0.99/1.19  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.99/1.19  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.99/1.19  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.99/1.19  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.99/1.19  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.99/1.19  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.99/1.19  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.99/1.19  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.99/1.19  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.99/1.19  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.99/1.19  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.99/1.19  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.99/1.19  fof(t110_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.99/1.19  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.99/1.19  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.99/1.19  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.99/1.19  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.99/1.19  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.99/1.19  fof(c_0_19, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t81_zfmisc_1])).
% 0.99/1.19  fof(c_0_20, plain, ![X58, X59]:k3_tarski(k2_tarski(X58,X59))=k2_xboole_0(X58,X59), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.99/1.19  fof(c_0_21, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.99/1.19  fof(c_0_22, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.99/1.19  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.99/1.19  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.99/1.19  fof(c_0_25, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.99/1.19  fof(c_0_26, plain, ![X36, X37, X38, X39]:k3_enumset1(X36,X36,X37,X38,X39)=k2_enumset1(X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.99/1.19  fof(c_0_27, plain, ![X40, X41, X42, X43, X44]:k4_enumset1(X40,X40,X41,X42,X43,X44)=k3_enumset1(X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.99/1.19  fof(c_0_28, plain, ![X45, X46, X47, X48, X49, X50]:k5_enumset1(X45,X45,X46,X47,X48,X49,X50)=k4_enumset1(X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.99/1.19  fof(c_0_29, plain, ![X51, X52, X53, X54, X55, X56, X57]:k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57)=k5_enumset1(X51,X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.99/1.19  fof(c_0_30, plain, ![X29, X30]:k2_xboole_0(X29,X30)=k5_xboole_0(X29,k4_xboole_0(X30,X29)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.99/1.19  fof(c_0_31, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.99/1.19  fof(c_0_32, plain, ![X22, X23, X24]:(~r1_tarski(X22,k3_xboole_0(X23,X24))|r1_tarski(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.99/1.19  fof(c_0_33, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.99/1.19  cnf(c_0_34, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.99/1.19  cnf(c_0_35, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.99/1.19  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.99/1.19  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.99/1.19  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.99/1.19  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.99/1.19  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.99/1.19  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.99/1.19  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.99/1.19  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.99/1.19  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.99/1.19  fof(c_0_45, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.99/1.19  cnf(c_0_46, negated_conjecture, (~r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k3_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.99/1.19  cnf(c_0_47, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_35]), c_0_42]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.99/1.19  fof(c_0_48, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X19,X18)|r1_tarski(k5_xboole_0(X17,X19),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).
% 0.99/1.19  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.99/1.19  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.99/1.19  fof(c_0_51, plain, ![X20, X21]:r1_tarski(k3_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.99/1.19  cnf(c_0_52, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(esk1_0),k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_44]), c_0_47]), c_0_44])).
% 0.99/1.19  cnf(c_0_53, plain, (r1_tarski(k5_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.99/1.19  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.99/1.19  cnf(c_0_55, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.99/1.19  fof(c_0_56, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.99/1.19  cnf(c_0_57, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))|~r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.99/1.19  cnf(c_0_58, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.99/1.19  fof(c_0_59, plain, ![X60, X61]:(~r1_tarski(X60,X61)|r1_tarski(k1_zfmisc_1(X60),k1_zfmisc_1(X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.99/1.19  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.99/1.19  fof(c_0_61, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|r1_tarski(X14,k2_xboole_0(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.99/1.19  cnf(c_0_62, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))|~r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_53]), c_0_58])).
% 0.99/1.19  cnf(c_0_63, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.99/1.19  cnf(c_0_64, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.99/1.19  cnf(c_0_65, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.99/1.19  cnf(c_0_66, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))|~r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.99/1.19  cnf(c_0_67, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_64, c_0_47])).
% 0.99/1.19  cnf(c_0_68, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.99/1.19  fof(c_0_69, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.99/1.19  cnf(c_0_70, negated_conjecture, (~r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))|~r1_tarski(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_66, c_0_63])).
% 0.99/1.19  cnf(c_0_71, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_67, c_0_44])).
% 0.99/1.19  cnf(c_0_72, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_68, c_0_47])).
% 0.99/1.19  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.99/1.19  cnf(c_0_74, negated_conjecture, (~r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.99/1.19  cnf(c_0_75, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_72, c_0_44])).
% 0.99/1.19  cnf(c_0_76, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 0.99/1.19  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])]), ['proof']).
% 0.99/1.19  # SZS output end CNFRefutation
% 0.99/1.19  # Proof object total steps             : 78
% 0.99/1.19  # Proof object clause steps            : 39
% 0.99/1.19  # Proof object formula steps           : 39
% 0.99/1.19  # Proof object conjectures             : 12
% 0.99/1.19  # Proof object clause conjectures      : 9
% 0.99/1.19  # Proof object formula conjectures     : 3
% 0.99/1.19  # Proof object initial clauses used    : 19
% 0.99/1.19  # Proof object initial formulas used   : 19
% 0.99/1.19  # Proof object generating inferences   : 12
% 0.99/1.19  # Proof object simplifying inferences  : 42
% 0.99/1.19  # Training examples: 0 positive, 0 negative
% 0.99/1.19  # Parsed axioms                        : 19
% 0.99/1.19  # Removed by relevancy pruning/SinE    : 0
% 0.99/1.19  # Initial clauses                      : 21
% 0.99/1.19  # Removed in clause preprocessing      : 8
% 0.99/1.19  # Initial clauses in saturation        : 13
% 0.99/1.19  # Processed clauses                    : 4472
% 0.99/1.19  # ...of these trivial                  : 184
% 0.99/1.19  # ...subsumed                          : 3144
% 0.99/1.19  # ...remaining for further processing  : 1144
% 0.99/1.19  # Other redundant clauses eliminated   : 2
% 0.99/1.19  # Clauses deleted for lack of memory   : 0
% 0.99/1.19  # Backward-subsumed                    : 12
% 0.99/1.19  # Backward-rewritten                   : 7
% 0.99/1.19  # Generated clauses                    : 86616
% 0.99/1.19  # ...of the previous two non-trivial   : 85860
% 0.99/1.19  # Contextual simplify-reflections      : 15
% 0.99/1.19  # Paramodulations                      : 86614
% 0.99/1.19  # Factorizations                       : 0
% 0.99/1.19  # Equation resolutions                 : 2
% 0.99/1.19  # Propositional unsat checks           : 0
% 0.99/1.19  #    Propositional check models        : 0
% 0.99/1.19  #    Propositional check unsatisfiable : 0
% 0.99/1.19  #    Propositional clauses             : 0
% 0.99/1.19  #    Propositional clauses after purity: 0
% 0.99/1.19  #    Propositional unsat core size     : 0
% 0.99/1.19  #    Propositional preprocessing time  : 0.000
% 0.99/1.19  #    Propositional encoding time       : 0.000
% 0.99/1.19  #    Propositional solver time         : 0.000
% 0.99/1.19  #    Success case prop preproc time    : 0.000
% 0.99/1.19  #    Success case prop encoding time   : 0.000
% 0.99/1.19  #    Success case prop solver time     : 0.000
% 0.99/1.19  # Current number of processed clauses  : 1111
% 0.99/1.19  #    Positive orientable unit clauses  : 89
% 0.99/1.19  #    Positive unorientable unit clauses: 3
% 0.99/1.19  #    Negative unit clauses             : 5
% 0.99/1.19  #    Non-unit-clauses                  : 1014
% 0.99/1.19  # Current number of unprocessed clauses: 81365
% 0.99/1.19  # ...number of literals in the above   : 215644
% 0.99/1.19  # Current number of archived formulas  : 0
% 0.99/1.19  # Current number of archived clauses   : 39
% 0.99/1.19  # Clause-clause subsumption calls (NU) : 165466
% 0.99/1.19  # Rec. Clause-clause subsumption calls : 151598
% 0.99/1.19  # Non-unit clause-clause subsumptions  : 3153
% 0.99/1.19  # Unit Clause-clause subsumption calls : 464
% 0.99/1.19  # Rewrite failures with RHS unbound    : 0
% 0.99/1.19  # BW rewrite match attempts            : 1953
% 0.99/1.19  # BW rewrite match successes           : 18
% 0.99/1.19  # Condensation attempts                : 0
% 0.99/1.19  # Condensation successes               : 0
% 0.99/1.19  # Termbank termtop insertions          : 1617296
% 1.03/1.20  
% 1.03/1.20  # -------------------------------------------------
% 1.03/1.20  # User time                : 0.814 s
% 1.03/1.20  # System time              : 0.036 s
% 1.03/1.20  # Total time               : 0.851 s
% 1.03/1.20  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
