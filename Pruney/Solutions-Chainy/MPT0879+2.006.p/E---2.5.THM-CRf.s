%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:40 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 431 expanded)
%              Number of clauses        :   22 ( 162 expanded)
%              Number of leaves         :   13 ( 134 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 455 expanded)
%              Number of equality atoms :   52 ( 454 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_mcart_1,conjecture,(
    ! [X1,X2,X3] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t83_enumset1,axiom,(
    ! [X1,X2] : k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k3_mcart_1(X1,X2,X3)) ),
    inference(assume_negation,[status(cth)],[t39_mcart_1])).

fof(c_0_14,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0)) != k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X26] : k1_enumset1(X26,X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X36,X37,X38] : k3_zfmisc_1(X36,X37,X38) = k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X27,X28,X29,X30] : k4_enumset1(X27,X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_19,plain,(
    ! [X13,X14,X15,X16,X17,X18] : k5_enumset1(X13,X13,X14,X15,X16,X17,X18) = k4_enumset1(X13,X14,X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25] : k6_enumset1(X19,X19,X20,X21,X22,X23,X24,X25) = k5_enumset1(X19,X20,X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_21,plain,(
    ! [X31,X32] : k3_enumset1(X31,X31,X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t83_enumset1])).

fof(c_0_22,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X33,X34,X35] :
      ( k2_zfmisc_1(k1_tarski(X33),k2_tarski(X34,X35)) = k2_tarski(k4_tarski(X33,X34),k4_tarski(X33,X35))
      & k2_zfmisc_1(k2_tarski(X33,X34),k1_tarski(X35)) = k2_tarski(k4_tarski(X33,X35),k4_tarski(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_24,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0)) != k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X43,X44,X45,X46] : k4_mcart_1(X43,X44,X45,X46) = k4_tarski(k4_tarski(k4_tarski(X43,X44),X45),X46) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

fof(c_0_35,plain,(
    ! [X39,X40,X41,X42] : k4_mcart_1(X39,X40,X41,X42) = k4_tarski(k3_mcart_1(X39,X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) != k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_26]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_32]),c_0_32]),c_0_26]),c_0_26]),c_0_26]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30])).

fof(c_0_39,plain,(
    ! [X47,X48] :
      ( k1_mcart_1(k4_tarski(X47,X48)) = X47
      & k2_mcart_1(k4_tarski(X47,X48)) = X48 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_40,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k3_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_44,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k4_tarski(k3_mcart_1(X1,X2,X3),X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k3_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0)) != k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43])).

cnf(c_0_47,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t39_mcart_1, conjecture, ![X1, X2, X3]:k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3))=k1_tarski(k3_mcart_1(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_mcart_1)).
% 0.13/0.37  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(t83_enumset1, axiom, ![X1, X2]:k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.13/0.37  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.13/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.13/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3))=k1_tarski(k3_mcart_1(X1,X2,X3))), inference(assume_negation,[status(cth)],[t39_mcart_1])).
% 0.13/0.37  fof(c_0_14, negated_conjecture, k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0))!=k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X26]:k1_enumset1(X26,X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.13/0.37  fof(c_0_16, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_17, plain, ![X36, X37, X38]:k3_zfmisc_1(X36,X37,X38)=k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_18, plain, ![X27, X28, X29, X30]:k4_enumset1(X27,X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 0.13/0.37  fof(c_0_19, plain, ![X13, X14, X15, X16, X17, X18]:k5_enumset1(X13,X13,X14,X15,X16,X17,X18)=k4_enumset1(X13,X14,X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.37  fof(c_0_20, plain, ![X19, X20, X21, X22, X23, X24, X25]:k6_enumset1(X19,X19,X20,X21,X22,X23,X24,X25)=k5_enumset1(X19,X20,X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_21, plain, ![X31, X32]:k3_enumset1(X31,X31,X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t83_enumset1])).
% 0.13/0.37  fof(c_0_22, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_23, plain, ![X33, X34, X35]:(k2_zfmisc_1(k1_tarski(X33),k2_tarski(X34,X35))=k2_tarski(k4_tarski(X33,X34),k4_tarski(X33,X35))&k2_zfmisc_1(k2_tarski(X33,X34),k1_tarski(X35))=k2_tarski(k4_tarski(X33,X35),k4_tarski(X34,X35))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0))!=k1_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_27, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_30, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_33, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  fof(c_0_34, plain, ![X43, X44, X45, X46]:k4_mcart_1(X43,X44,X45,X46)=k4_tarski(k4_tarski(k4_tarski(X43,X44),X45),X46), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.13/0.37  fof(c_0_35, plain, ![X39, X40, X41, X42]:k4_mcart_1(X39,X40,X41,X42)=k4_tarski(k3_mcart_1(X39,X40,X41),X42), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))!=k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.37  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_26]), c_0_28]), c_0_29]), c_0_30])).
% 0.13/0.37  cnf(c_0_38, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))=k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_32]), c_0_32]), c_0_26]), c_0_26]), c_0_26]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.37  fof(c_0_39, plain, ![X47, X48]:(k1_mcart_1(k4_tarski(X47,X48))=X47&k2_mcart_1(k4_tarski(X47,X48))=X48), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.37  cnf(c_0_40, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_41, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k3_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0))!=k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.13/0.37  cnf(c_0_43, plain, (k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))=k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_37]), c_0_37]), c_0_37])).
% 0.13/0.37  cnf(c_0_44, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_45, plain, (k4_tarski(k3_mcart_1(X1,X2,X3),X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (k3_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0))!=k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43])).
% 0.13/0.37  cnf(c_0_47, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_44])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 49
% 0.13/0.37  # Proof object clause steps            : 22
% 0.13/0.37  # Proof object formula steps           : 27
% 0.13/0.37  # Proof object conjectures             : 8
% 0.13/0.37  # Proof object clause conjectures      : 5
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 13
% 0.13/0.37  # Proof object generating inferences   : 1
% 0.13/0.37  # Proof object simplifying inferences  : 58
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 13
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 15
% 0.13/0.37  # Removed in clause preprocessing      : 8
% 0.13/0.37  # Initial clauses in saturation        : 7
% 0.13/0.37  # Processed clauses                    : 14
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 13
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.37  # Generated clauses                    : 2
% 0.13/0.37  # ...of the previous two non-trivial   : 3
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 2
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
% 0.13/0.37  # Current number of processed clauses  : 3
% 0.13/0.37  #    Positive orientable unit clauses  : 3
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 3
% 0.13/0.37  # ...number of literals in the above   : 3
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 18
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 7
% 0.13/0.37  # BW rewrite match successes           : 6
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 896
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.030 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
