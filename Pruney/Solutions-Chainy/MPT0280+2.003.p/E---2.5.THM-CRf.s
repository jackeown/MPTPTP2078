%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 264 expanded)
%              Number of clauses        :   33 ( 109 expanded)
%              Number of leaves         :   16 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 290 expanded)
%              Number of equality atoms :   37 ( 224 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t81_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

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

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t110_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_16,plain,(
    ! [X52,X53] : k3_tarski(k2_tarski(X52,X53)) = k2_xboole_0(X52,X53) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t81_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33] : k3_enumset1(X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X34,X35,X36,X37,X38] : k4_enumset1(X34,X34,X35,X36,X37,X38) = k3_enumset1(X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X39,X40,X41,X42,X43,X44] : k5_enumset1(X39,X39,X40,X41,X42,X43,X44) = k4_enumset1(X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] : k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51) = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k3_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_40,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_41,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X16)
      | r1_tarski(k5_xboole_0(X15,X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).

fof(c_0_42,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(k3_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

fof(c_0_43,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(esk1_0),k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_45,plain,
    ( r1_tarski(k5_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))
    | ~ r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_51,plain,(
    ! [X54,X55] :
      ( ~ r1_tarski(X54,X55)
      | r1_tarski(k1_zfmisc_1(X54),k1_zfmisc_1(X55)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))
    | ~ r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_50])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

fof(c_0_56,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))
    | ~ r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_40])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_47])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_58])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t81_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 0.13/0.37  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.13/0.37  fof(t110_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.13/0.37  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.13/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.37  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.13/0.37  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.13/0.37  fof(c_0_16, plain, ![X52, X53]:k3_tarski(k2_tarski(X52,X53))=k2_xboole_0(X52,X53), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.37  fof(c_0_17, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_18, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)),k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t81_zfmisc_1])).
% 0.13/0.37  fof(c_0_19, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.37  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  fof(c_0_22, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_23, plain, ![X30, X31, X32, X33]:k3_enumset1(X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_24, plain, ![X34, X35, X36, X37, X38]:k4_enumset1(X34,X34,X35,X36,X37,X38)=k3_enumset1(X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.37  fof(c_0_25, plain, ![X39, X40, X41, X42, X43, X44]:k5_enumset1(X39,X39,X40,X41,X42,X43,X44)=k4_enumset1(X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.37  fof(c_0_26, plain, ![X45, X46, X47, X48, X49, X50, X51]:k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51)=k5_enumset1(X45,X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_27, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.13/0.37  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_32, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_33, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_34, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  fof(c_0_35, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_37, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.13/0.37  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (~r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k3_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.13/0.37  cnf(c_0_40, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.37  fof(c_0_41, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X17,X16)|r1_tarski(k5_xboole_0(X15,X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_xboole_1])])).
% 0.13/0.37  fof(c_0_42, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(k3_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.13/0.37  fof(c_0_43, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(esk1_0),k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_40])).
% 0.13/0.37  cnf(c_0_45, plain, (r1_tarski(k5_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.37  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.37  fof(c_0_48, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (~r1_tarski(k5_xboole_0(k1_zfmisc_1(esk2_0),k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))|~r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.37  cnf(c_0_50, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.37  fof(c_0_51, plain, ![X54, X55]:(~r1_tarski(X54,X55)|r1_tarski(k1_zfmisc_1(X54),k1_zfmisc_1(X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.13/0.37  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))|~r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_50])).
% 0.13/0.37  cnf(c_0_54, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.37  cnf(c_0_55, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.13/0.37  fof(c_0_56, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk1_0),k1_zfmisc_1(k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))))|~r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.37  cnf(c_0_58, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_55, c_0_40])).
% 0.13/0.37  cnf(c_0_59, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.37  cnf(c_0_60, negated_conjecture, (~r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))|~r1_tarski(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_57, c_0_54])).
% 0.13/0.37  cnf(c_0_61, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_58, c_0_47])).
% 0.13/0.37  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_38, c_0_59])).
% 0.13/0.37  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_58])])).
% 0.13/0.37  cnf(c_0_64, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_59])).
% 0.13/0.37  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 66
% 0.13/0.37  # Proof object clause steps            : 33
% 0.13/0.37  # Proof object formula steps           : 33
% 0.13/0.37  # Proof object conjectures             : 12
% 0.13/0.37  # Proof object clause conjectures      : 9
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 16
% 0.13/0.37  # Proof object initial formulas used   : 16
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 34
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 16
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 16
% 0.13/0.37  # Removed in clause preprocessing      : 7
% 0.13/0.37  # Initial clauses in saturation        : 9
% 0.13/0.37  # Processed clauses                    : 36
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 5
% 0.13/0.37  # ...remaining for further processing  : 30
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 4
% 0.13/0.37  # Generated clauses                    : 70
% 0.13/0.37  # ...of the previous two non-trivial   : 61
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 70
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 17
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 4
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 6
% 0.13/0.37  # Current number of unprocessed clauses: 42
% 0.13/0.37  # ...number of literals in the above   : 50
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 20
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 41
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 40
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.37  # Unit Clause-clause subsumption calls : 6
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 51
% 0.13/0.37  # BW rewrite match successes           : 42
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1541
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
