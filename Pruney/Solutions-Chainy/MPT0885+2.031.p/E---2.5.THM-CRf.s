%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:51 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 163 expanded)
%              Number of clauses        :   21 (  68 expanded)
%              Number of leaves         :    8 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 ( 185 expanded)
%              Number of equality atoms :   39 ( 184 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t45_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9] : k2_enumset1(X6,X7,X8,X9) = k2_enumset1(X6,X8,X7,X9) ),
    inference(variable_rename,[status(thm)],[t104_enumset1])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13] : k2_enumset1(X10,X11,X12,X13) = k2_xboole_0(k2_tarski(X10,X11),k2_tarski(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_10,plain,(
    ! [X19,X20,X21] :
      ( k2_zfmisc_1(k1_tarski(X19),k2_tarski(X20,X21)) = k2_tarski(k4_tarski(X19,X20),k4_tarski(X19,X21))
      & k2_zfmisc_1(k2_tarski(X19,X20),k1_tarski(X21)) = k2_tarski(k4_tarski(X19,X21),k4_tarski(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X14] : k2_enumset1(X14,X14,X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18] : k2_zfmisc_1(k2_tarski(X15,X16),k2_tarski(X17,X18)) = k2_enumset1(k4_tarski(X15,X17),k4_tarski(X15,X18),k4_tarski(X16,X17),k4_tarski(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t45_mcart_1])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_14])).

fof(c_0_21,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] : k3_mcart_1(X22,X23,X24) = k4_tarski(k4_tarski(X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_23,plain,(
    ! [X25,X26,X27] : k3_zfmisc_1(X25,X26,X27) = k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(k4_tarski(X1,X3),k4_tarski(X1,X4)),k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k2_tarski(X1,k4_tarski(X2,X3)),k2_tarski(X4,k4_tarski(X2,X5))) = k2_xboole_0(k2_tarski(X1,X4),k2_zfmisc_1(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)),k2_tarski(X3,X5))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X3,X4)),k2_zfmisc_1(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)),k2_tarski(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_20])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)),k2_tarski(k4_tarski(X1,X5),k4_tarski(X3,X6))) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X5)),k2_zfmisc_1(k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3)),k2_tarski(X4,X6))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3))) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk4_0,esk5_0)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0)),k2_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_16]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_14]),c_0_14])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3))),k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X4,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_xboole_0(k2_tarski(esk5_0,esk5_0),k2_tarski(esk5_0,esk5_0)))) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32]),c_0_32]),c_0_20]),c_0_20])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3)),k2_tarski(X4,X5)) = k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X4,X4))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X5,X5)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.96/2.21  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 1.96/2.21  # and selection function SelectNewComplexAHP.
% 1.96/2.21  #
% 1.96/2.21  # Preprocessing time       : 0.026 s
% 1.96/2.21  # Presaturation interreduction done
% 1.96/2.21  
% 1.96/2.21  # Proof found!
% 1.96/2.21  # SZS status Theorem
% 1.96/2.21  # SZS output start CNFRefutation
% 1.96/2.21  fof(t104_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X2,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 1.96/2.21  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 1.96/2.21  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 1.96/2.21  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 1.96/2.21  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 1.96/2.21  fof(t45_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_mcart_1)).
% 1.96/2.21  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.96/2.21  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.96/2.21  fof(c_0_8, plain, ![X6, X7, X8, X9]:k2_enumset1(X6,X7,X8,X9)=k2_enumset1(X6,X8,X7,X9), inference(variable_rename,[status(thm)],[t104_enumset1])).
% 1.96/2.21  fof(c_0_9, plain, ![X10, X11, X12, X13]:k2_enumset1(X10,X11,X12,X13)=k2_xboole_0(k2_tarski(X10,X11),k2_tarski(X12,X13)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 1.96/2.21  fof(c_0_10, plain, ![X19, X20, X21]:(k2_zfmisc_1(k1_tarski(X19),k2_tarski(X20,X21))=k2_tarski(k4_tarski(X19,X20),k4_tarski(X19,X21))&k2_zfmisc_1(k2_tarski(X19,X20),k1_tarski(X21))=k2_tarski(k4_tarski(X19,X21),k4_tarski(X20,X21))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 1.96/2.21  fof(c_0_11, plain, ![X14]:k2_enumset1(X14,X14,X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 1.96/2.21  fof(c_0_12, plain, ![X15, X16, X17, X18]:k2_zfmisc_1(k2_tarski(X15,X16),k2_tarski(X17,X18))=k2_enumset1(k4_tarski(X15,X17),k4_tarski(X15,X18),k4_tarski(X16,X17),k4_tarski(X16,X18)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 1.96/2.21  cnf(c_0_13, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.96/2.21  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.96/2.21  cnf(c_0_15, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.96/2.21  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.96/2.21  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))), inference(assume_negation,[status(cth)],[t45_mcart_1])).
% 1.96/2.21  cnf(c_0_18, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.96/2.21  cnf(c_0_19, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 1.96/2.21  cnf(c_0_20, plain, (k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_14])).
% 1.96/2.21  fof(c_0_21, negated_conjecture, k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.96/2.21  fof(c_0_22, plain, ![X22, X23, X24]:k3_mcart_1(X22,X23,X24)=k4_tarski(k4_tarski(X22,X23),X24), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 1.96/2.21  fof(c_0_23, plain, ![X25, X26, X27]:k3_zfmisc_1(X25,X26,X27)=k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 1.96/2.21  cnf(c_0_24, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_xboole_0(k2_tarski(k4_tarski(X1,X3),k4_tarski(X1,X4)),k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X4)))), inference(rw,[status(thm)],[c_0_18, c_0_14])).
% 1.96/2.21  cnf(c_0_25, plain, (k2_xboole_0(k2_tarski(X1,k4_tarski(X2,X3)),k2_tarski(X4,k4_tarski(X2,X5)))=k2_xboole_0(k2_tarski(X1,X4),k2_zfmisc_1(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)),k2_tarski(X3,X5)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.96/2.21  cnf(c_0_26, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.96/2.21  cnf(c_0_27, negated_conjecture, (k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.96/2.21  cnf(c_0_28, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.96/2.21  cnf(c_0_29, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.96/2.21  cnf(c_0_30, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X3,X4)),k2_zfmisc_1(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)),k2_tarski(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_20])).
% 1.96/2.21  cnf(c_0_31, plain, (k2_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)),k2_tarski(k4_tarski(X1,X5),k4_tarski(X3,X6)))=k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X5)),k2_zfmisc_1(k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3)),k2_tarski(X4,X6)))), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 1.96/2.21  cnf(c_0_32, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3)))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_14])).
% 1.96/2.21  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk4_0,esk5_0))!=k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0)),k2_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_16]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_14]), c_0_14])).
% 1.96/2.21  cnf(c_0_34, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_xboole_0(k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3))),k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X4,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_32])).
% 1.96/2.21  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_xboole_0(k2_tarski(esk5_0,esk5_0),k2_tarski(esk5_0,esk5_0))))!=k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk1_0,esk1_0)),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_32]), c_0_32]), c_0_20]), c_0_20])).
% 1.96/2.21  cnf(c_0_36, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3)),k2_tarski(X4,X5))=k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X4,X4))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X5,X5))))), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 1.96/2.21  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 1.96/2.21  # SZS output end CNFRefutation
% 1.96/2.21  # Proof object total steps             : 38
% 1.96/2.21  # Proof object clause steps            : 21
% 1.96/2.21  # Proof object formula steps           : 17
% 1.96/2.21  # Proof object conjectures             : 7
% 1.96/2.21  # Proof object clause conjectures      : 4
% 1.96/2.21  # Proof object formula conjectures     : 3
% 1.96/2.21  # Proof object initial clauses used    : 9
% 1.96/2.21  # Proof object initial formulas used   : 8
% 1.96/2.21  # Proof object generating inferences   : 4
% 1.96/2.21  # Proof object simplifying inferences  : 25
% 1.96/2.21  # Training examples: 0 positive, 0 negative
% 1.96/2.21  # Parsed axioms                        : 8
% 1.96/2.21  # Removed by relevancy pruning/SinE    : 0
% 1.96/2.21  # Initial clauses                      : 9
% 1.96/2.21  # Removed in clause preprocessing      : 4
% 1.96/2.21  # Initial clauses in saturation        : 5
% 1.96/2.21  # Processed clauses                    : 5100
% 1.96/2.21  # ...of these trivial                  : 539
% 1.96/2.21  # ...subsumed                          : 3947
% 1.96/2.21  # ...remaining for further processing  : 614
% 1.96/2.21  # Other redundant clauses eliminated   : 0
% 1.96/2.21  # Clauses deleted for lack of memory   : 0
% 1.96/2.21  # Backward-subsumed                    : 75
% 1.96/2.21  # Backward-rewritten                   : 20
% 1.96/2.21  # Generated clauses                    : 154244
% 1.96/2.21  # ...of the previous two non-trivial   : 146817
% 1.96/2.21  # Contextual simplify-reflections      : 0
% 1.96/2.21  # Paramodulations                      : 154244
% 1.96/2.21  # Factorizations                       : 0
% 1.96/2.21  # Equation resolutions                 : 0
% 1.96/2.21  # Propositional unsat checks           : 0
% 1.96/2.21  #    Propositional check models        : 0
% 1.96/2.21  #    Propositional check unsatisfiable : 0
% 1.96/2.21  #    Propositional clauses             : 0
% 1.96/2.21  #    Propositional clauses after purity: 0
% 1.96/2.21  #    Propositional unsat core size     : 0
% 1.96/2.21  #    Propositional preprocessing time  : 0.000
% 1.96/2.21  #    Propositional encoding time       : 0.000
% 1.96/2.21  #    Propositional solver time         : 0.000
% 1.96/2.21  #    Success case prop preproc time    : 0.000
% 1.96/2.21  #    Success case prop encoding time   : 0.000
% 1.96/2.21  #    Success case prop solver time     : 0.000
% 1.96/2.21  # Current number of processed clauses  : 514
% 1.96/2.21  #    Positive orientable unit clauses  : 120
% 1.96/2.21  #    Positive unorientable unit clauses: 394
% 1.96/2.21  #    Negative unit clauses             : 0
% 1.96/2.21  #    Non-unit-clauses                  : 0
% 1.96/2.21  # Current number of unprocessed clauses: 140821
% 1.96/2.21  # ...number of literals in the above   : 140821
% 1.96/2.21  # Current number of archived formulas  : 0
% 1.96/2.21  # Current number of archived clauses   : 104
% 1.96/2.21  # Clause-clause subsumption calls (NU) : 0
% 1.96/2.21  # Rec. Clause-clause subsumption calls : 0
% 1.96/2.21  # Non-unit clause-clause subsumptions  : 0
% 1.96/2.21  # Unit Clause-clause subsumption calls : 10538
% 1.96/2.21  # Rewrite failures with RHS unbound    : 0
% 1.96/2.21  # BW rewrite match attempts            : 8599
% 1.96/2.21  # BW rewrite match successes           : 554
% 1.96/2.21  # Condensation attempts                : 0
% 1.96/2.21  # Condensation successes               : 0
% 1.96/2.21  # Termbank termtop insertions          : 7297027
% 2.07/2.22  
% 2.07/2.22  # -------------------------------------------------
% 2.07/2.22  # User time                : 1.793 s
% 2.07/2.22  # System time              : 0.088 s
% 2.07/2.22  # Total time               : 1.881 s
% 2.07/2.22  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
