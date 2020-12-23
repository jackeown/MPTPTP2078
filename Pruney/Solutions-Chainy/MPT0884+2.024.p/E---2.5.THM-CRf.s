%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:45 EST 2020

% Result     : Theorem 1.03s
% Output     : CNFRefutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 735 expanded)
%              Number of clauses        :   29 ( 274 expanded)
%              Number of leaves         :   13 ( 230 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 ( 737 expanded)
%              Number of equality atoms :   57 ( 736 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(t137_enumset1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10] : k2_enumset1(X7,X8,X9,X10) = k2_xboole_0(k2_tarski(X7,X8),k2_tarski(X9,X10)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X14,X15,X16,X17,X18] : k3_enumset1(X14,X15,X16,X17,X18) = k2_xboole_0(k2_tarski(X14,X15),k1_enumset1(X16,X17,X18)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_21,plain,(
    ! [X11,X12,X13] : k2_xboole_0(k2_tarski(X12,X11),k2_tarski(X13,X11)) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t137_enumset1])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X2)) = k1_enumset1(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_17]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_17]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X2))) = k3_enumset1(X2,X2,X2,X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_17]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X2,X3,X3,X2) = k3_enumset1(X2,X2,X2,X1,X3) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X2,X2,X1,X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X1,X2,X3,X4,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_33]),c_0_29])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

fof(c_0_36,plain,(
    ! [X37,X38,X39,X40] : k2_zfmisc_1(k2_tarski(X37,X38),k2_tarski(X39,X40)) = k2_enumset1(k4_tarski(X37,X39),k4_tarski(X37,X40),k4_tarski(X38,X39),k4_tarski(X38,X40)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X2,X2,X1,X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_38,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

fof(c_0_39,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_40,plain,(
    ! [X44,X45,X46] : k3_mcart_1(X44,X45,X46) = k4_tarski(k4_tarski(X44,X45),X46) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_41,plain,(
    ! [X47,X48,X49] : k3_zfmisc_1(X47,X48,X49) = k2_zfmisc_1(k2_zfmisc_1(X47,X48),X49) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X2,X2,X2,X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

fof(c_0_44,plain,(
    ! [X41,X42,X43] :
      ( k2_zfmisc_1(k1_tarski(X41),k2_tarski(X42,X43)) = k2_tarski(k4_tarski(X41,X42),k4_tarski(X41,X43))
      & k2_zfmisc_1(k2_tarski(X41,X42),k1_tarski(X43)) = k2_tarski(k4_tarski(X41,X43),k4_tarski(X42,X43)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_45,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)) = k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_17]),c_0_17]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X4,X3,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_43]),c_0_29])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_17]),c_0_17]),c_0_17]),c_0_24]),c_0_24]),c_0_24]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_53,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4)) = k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X3),k3_enumset1(X2,X2,X2,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_46]),c_0_17]),c_0_17]),c_0_17]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.03/1.21  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 1.03/1.21  # and selection function SelectNewComplexAHP.
% 1.03/1.21  #
% 1.03/1.21  # Preprocessing time       : 0.026 s
% 1.03/1.21  # Presaturation interreduction done
% 1.03/1.21  
% 1.03/1.21  # Proof found!
% 1.03/1.21  # SZS status Theorem
% 1.03/1.21  # SZS output start CNFRefutation
% 1.03/1.21  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.03/1.21  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.03/1.21  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.03/1.21  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.03/1.21  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.03/1.21  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.03/1.21  fof(t137_enumset1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 1.03/1.21  fof(t44_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 1.03/1.21  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 1.03/1.21  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.03/1.21  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.03/1.21  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.03/1.21  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 1.03/1.21  fof(c_0_13, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.03/1.21  fof(c_0_14, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.03/1.21  fof(c_0_15, plain, ![X7, X8, X9, X10]:k2_enumset1(X7,X8,X9,X10)=k2_xboole_0(k2_tarski(X7,X8),k2_tarski(X9,X10)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 1.03/1.21  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.03/1.21  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.03/1.21  fof(c_0_18, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.03/1.21  fof(c_0_19, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.03/1.21  fof(c_0_20, plain, ![X14, X15, X16, X17, X18]:k3_enumset1(X14,X15,X16,X17,X18)=k2_xboole_0(k2_tarski(X14,X15),k1_enumset1(X16,X17,X18)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 1.03/1.21  fof(c_0_21, plain, ![X11, X12, X13]:k2_xboole_0(k2_tarski(X12,X11),k2_tarski(X13,X11))=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t137_enumset1])).
% 1.03/1.21  cnf(c_0_22, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.03/1.21  cnf(c_0_23, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 1.03/1.21  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.03/1.21  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.03/1.21  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.03/1.21  cnf(c_0_27, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X2))=k1_enumset1(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.03/1.21  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_17]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 1.03/1.21  cnf(c_0_29, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_17]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 1.03/1.21  cnf(c_0_30, plain, (k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X2)))=k3_enumset1(X2,X2,X2,X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_17]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 1.03/1.21  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 1.03/1.21  cnf(c_0_32, plain, (k3_enumset1(X1,X2,X3,X3,X2)=k3_enumset1(X2,X2,X2,X1,X3)), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 1.03/1.21  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X2,X2,X1,X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.03/1.21  cnf(c_0_34, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X1,X2,X3,X4,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_33]), c_0_29])).
% 1.03/1.21  fof(c_0_35, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5))), inference(assume_negation,[status(cth)],[t44_mcart_1])).
% 1.03/1.21  fof(c_0_36, plain, ![X37, X38, X39, X40]:k2_zfmisc_1(k2_tarski(X37,X38),k2_tarski(X39,X40))=k2_enumset1(k4_tarski(X37,X39),k4_tarski(X37,X40),k4_tarski(X38,X39),k4_tarski(X38,X40)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 1.03/1.21  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X2,X2,X1,X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.03/1.21  fof(c_0_38, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 1.03/1.21  fof(c_0_39, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.03/1.21  fof(c_0_40, plain, ![X44, X45, X46]:k3_mcart_1(X44,X45,X46)=k4_tarski(k4_tarski(X44,X45),X46), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 1.03/1.21  fof(c_0_41, plain, ![X47, X48, X49]:k3_zfmisc_1(X47,X48,X49)=k2_zfmisc_1(k2_zfmisc_1(X47,X48),X49), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 1.03/1.21  cnf(c_0_42, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.03/1.21  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X2,X2,X2,X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_37])).
% 1.03/1.21  fof(c_0_44, plain, ![X41, X42, X43]:(k2_zfmisc_1(k1_tarski(X41),k2_tarski(X42,X43))=k2_tarski(k4_tarski(X41,X42),k4_tarski(X41,X43))&k2_zfmisc_1(k2_tarski(X41,X42),k1_tarski(X43))=k2_tarski(k4_tarski(X41,X43),k4_tarski(X42,X43))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 1.03/1.21  cnf(c_0_45, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.03/1.21  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.03/1.21  cnf(c_0_47, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.03/1.21  cnf(c_0_48, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.03/1.21  cnf(c_0_49, plain, (k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))=k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_17]), c_0_17]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25])).
% 1.03/1.21  cnf(c_0_50, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X4,X3,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_43]), c_0_29])).
% 1.03/1.21  cnf(c_0_51, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.03/1.21  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_17]), c_0_17]), c_0_17]), c_0_24]), c_0_24]), c_0_24]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 1.03/1.21  cnf(c_0_53, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4))=k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X3),k3_enumset1(X2,X2,X2,X2,X4))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.03/1.21  cnf(c_0_54, plain, (k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))=k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_46]), c_0_17]), c_0_17]), c_0_17]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25])).
% 1.03/1.21  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), ['proof']).
% 1.03/1.21  # SZS output end CNFRefutation
% 1.03/1.21  # Proof object total steps             : 56
% 1.03/1.21  # Proof object clause steps            : 29
% 1.03/1.21  # Proof object formula steps           : 27
% 1.03/1.21  # Proof object conjectures             : 6
% 1.03/1.21  # Proof object clause conjectures      : 3
% 1.03/1.21  # Proof object formula conjectures     : 3
% 1.03/1.21  # Proof object initial clauses used    : 13
% 1.03/1.21  # Proof object initial formulas used   : 13
% 1.03/1.21  # Proof object generating inferences   : 6
% 1.03/1.21  # Proof object simplifying inferences  : 79
% 1.03/1.21  # Training examples: 0 positive, 0 negative
% 1.03/1.21  # Parsed axioms                        : 14
% 1.03/1.21  # Removed by relevancy pruning/SinE    : 0
% 1.03/1.21  # Initial clauses                      : 15
% 1.03/1.21  # Removed in clause preprocessing      : 7
% 1.03/1.21  # Initial clauses in saturation        : 8
% 1.03/1.21  # Processed clauses                    : 23249
% 1.03/1.21  # ...of these trivial                  : 295
% 1.03/1.21  # ...subsumed                          : 22530
% 1.03/1.21  # ...remaining for further processing  : 424
% 1.03/1.21  # Other redundant clauses eliminated   : 0
% 1.03/1.21  # Clauses deleted for lack of memory   : 0
% 1.03/1.21  # Backward-subsumed                    : 67
% 1.03/1.21  # Backward-rewritten                   : 13
% 1.03/1.21  # Generated clauses                    : 254165
% 1.03/1.21  # ...of the previous two non-trivial   : 117593
% 1.03/1.21  # Contextual simplify-reflections      : 0
% 1.03/1.21  # Paramodulations                      : 254165
% 1.03/1.21  # Factorizations                       : 0
% 1.03/1.21  # Equation resolutions                 : 0
% 1.03/1.21  # Propositional unsat checks           : 0
% 1.03/1.21  #    Propositional check models        : 0
% 1.03/1.21  #    Propositional check unsatisfiable : 0
% 1.03/1.21  #    Propositional clauses             : 0
% 1.03/1.21  #    Propositional clauses after purity: 0
% 1.03/1.21  #    Propositional unsat core size     : 0
% 1.03/1.21  #    Propositional preprocessing time  : 0.000
% 1.03/1.21  #    Propositional encoding time       : 0.000
% 1.03/1.21  #    Propositional solver time         : 0.000
% 1.03/1.21  #    Success case prop preproc time    : 0.000
% 1.03/1.21  #    Success case prop encoding time   : 0.000
% 1.03/1.21  #    Success case prop solver time     : 0.000
% 1.03/1.21  # Current number of processed clauses  : 336
% 1.03/1.21  #    Positive orientable unit clauses  : 77
% 1.03/1.21  #    Positive unorientable unit clauses: 259
% 1.03/1.21  #    Negative unit clauses             : 0
% 1.03/1.21  #    Non-unit-clauses                  : 0
% 1.03/1.21  # Current number of unprocessed clauses: 86979
% 1.03/1.21  # ...number of literals in the above   : 86979
% 1.03/1.21  # Current number of archived formulas  : 0
% 1.03/1.21  # Current number of archived clauses   : 95
% 1.03/1.21  # Clause-clause subsumption calls (NU) : 0
% 1.03/1.21  # Rec. Clause-clause subsumption calls : 0
% 1.03/1.21  # Non-unit clause-clause subsumptions  : 0
% 1.03/1.21  # Unit Clause-clause subsumption calls : 54936
% 1.03/1.21  # Rewrite failures with RHS unbound    : 0
% 1.03/1.21  # BW rewrite match attempts            : 73056
% 1.03/1.21  # BW rewrite match successes           : 11710
% 1.03/1.21  # Condensation attempts                : 0
% 1.03/1.21  # Condensation successes               : 0
% 1.03/1.21  # Termbank termtop insertions          : 1780599
% 1.05/1.21  
% 1.05/1.21  # -------------------------------------------------
% 1.05/1.21  # User time                : 0.831 s
% 1.05/1.21  # System time              : 0.030 s
% 1.05/1.21  # Total time               : 0.861 s
% 1.05/1.21  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
