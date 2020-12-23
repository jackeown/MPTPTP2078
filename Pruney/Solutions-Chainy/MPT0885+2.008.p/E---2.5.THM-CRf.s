%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:48 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 260 expanded)
%              Number of clauses        :   26 ( 103 expanded)
%              Number of leaves         :   11 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 ( 276 expanded)
%              Number of equality atoms :   50 ( 275 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t45_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_11,plain,(
    ! [X18,X19] : k3_tarski(k2_tarski(X18,X19)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14] : k2_enumset1(X11,X12,X13,X14) = k2_xboole_0(k1_tarski(X11),k1_enumset1(X12,X13,X14)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_14,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_15,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X20,X21,X22,X23] : k2_zfmisc_1(k2_tarski(X20,X21),k2_tarski(X22,X23)) = k2_enumset1(k4_tarski(X20,X22),k4_tarski(X20,X23),k4_tarski(X21,X22),k4_tarski(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( k2_zfmisc_1(k1_tarski(X24),k2_tarski(X25,X26)) = k2_tarski(k4_tarski(X24,X25),k4_tarski(X24,X26))
      & k2_zfmisc_1(k2_tarski(X24,X25),k1_tarski(X26)) = k2_tarski(k4_tarski(X24,X26),k4_tarski(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X8,X9,X10] : k1_enumset1(X8,X9,X10) = k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_23,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t45_mcart_1])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_16]),c_0_20])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_31,plain,(
    ! [X27,X28,X29] : k3_mcart_1(X27,X28,X29) = k4_tarski(k4_tarski(X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_32,plain,(
    ! [X30,X31,X32] : k3_zfmisc_1(X30,X31,X32) = k2_zfmisc_1(k2_zfmisc_1(X30,X31),X32) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_16]),c_0_16]),c_0_26])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3)) = k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_19]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_16]),c_0_16]),c_0_20])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_16]),c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X3)))) = k2_zfmisc_1(k1_enumset1(X1,X1,X4),k1_enumset1(X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0)),k1_enumset1(esk4_0,esk4_0,esk5_0)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_19]),c_0_16]),c_0_16]),c_0_16]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_26])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)) = k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_19]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_45,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4)))) = k2_zfmisc_1(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk2_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk2_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0)),k1_enumset1(esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_47,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),k1_enumset1(k4_tarski(X4,X3),k4_tarski(k4_tarski(X1,X2),X5),k4_tarski(X4,X5)))) = k2_zfmisc_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),X4),k1_enumset1(X3,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.48  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.21/0.48  # and selection function SelectNewComplexAHP.
% 0.21/0.48  #
% 0.21/0.48  # Preprocessing time       : 0.026 s
% 0.21/0.48  # Presaturation interreduction done
% 0.21/0.48  
% 0.21/0.48  # Proof found!
% 0.21/0.48  # SZS status Theorem
% 0.21/0.48  # SZS output start CNFRefutation
% 0.21/0.48  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.48  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.21/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.48  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.21/0.48  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.21/0.48  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.21/0.48  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.48  fof(t45_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_mcart_1)).
% 0.21/0.48  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.48  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.48  fof(c_0_11, plain, ![X18, X19]:k3_tarski(k2_tarski(X18,X19))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.48  fof(c_0_12, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.48  fof(c_0_13, plain, ![X11, X12, X13, X14]:k2_enumset1(X11,X12,X13,X14)=k2_xboole_0(k1_tarski(X11),k1_enumset1(X12,X13,X14)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.21/0.48  fof(c_0_14, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.48  cnf(c_0_15, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.48  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.48  fof(c_0_17, plain, ![X20, X21, X22, X23]:k2_zfmisc_1(k2_tarski(X20,X21),k2_tarski(X22,X23))=k2_enumset1(k4_tarski(X20,X22),k4_tarski(X20,X23),k4_tarski(X21,X22),k4_tarski(X21,X23)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 0.21/0.48  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.48  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.48  cnf(c_0_20, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.48  fof(c_0_21, plain, ![X24, X25, X26]:(k2_zfmisc_1(k1_tarski(X24),k2_tarski(X25,X26))=k2_tarski(k4_tarski(X24,X25),k4_tarski(X24,X26))&k2_zfmisc_1(k2_tarski(X24,X25),k1_tarski(X26))=k2_tarski(k4_tarski(X24,X26),k4_tarski(X25,X26))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.21/0.48  fof(c_0_22, plain, ![X8, X9, X10]:k1_enumset1(X8,X9,X10)=k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.21/0.48  fof(c_0_23, plain, ![X6, X7]:k2_tarski(X6,X7)=k2_tarski(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.48  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))), inference(assume_negation,[status(cth)],[t45_mcart_1])).
% 0.21/0.48  cnf(c_0_25, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.48  cnf(c_0_26, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_16]), c_0_20])).
% 0.21/0.48  cnf(c_0_27, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.48  cnf(c_0_28, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.48  cnf(c_0_29, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.48  fof(c_0_30, negated_conjecture, k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.21/0.48  fof(c_0_31, plain, ![X27, X28, X29]:k3_mcart_1(X27,X28,X29)=k4_tarski(k4_tarski(X27,X28),X29), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.48  fof(c_0_32, plain, ![X30, X31, X32]:k3_zfmisc_1(X30,X31,X32)=k2_zfmisc_1(k2_zfmisc_1(X30,X31),X32), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.48  cnf(c_0_33, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4))=k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_16]), c_0_16]), c_0_26])).
% 0.21/0.48  cnf(c_0_34, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3))=k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_19]), c_0_16]), c_0_16]), c_0_16])).
% 0.21/0.48  cnf(c_0_35, plain, (k1_enumset1(X1,X2,X3)=k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_16]), c_0_16]), c_0_20])).
% 0.21/0.48  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_16]), c_0_16])).
% 0.21/0.48  cnf(c_0_37, negated_conjecture, (k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.48  cnf(c_0_38, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.48  cnf(c_0_39, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.48  cnf(c_0_40, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.48  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X3))))=k2_zfmisc_1(k1_enumset1(X1,X1,X4),k1_enumset1(X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34])).
% 0.21/0.48  cnf(c_0_42, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_35])).
% 0.21/0.48  cnf(c_0_43, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0)),k1_enumset1(esk4_0,esk4_0,esk5_0))!=k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_19]), c_0_16]), c_0_16]), c_0_16]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_26])).
% 0.21/0.48  cnf(c_0_44, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3))=k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_19]), c_0_16]), c_0_16]), c_0_16])).
% 0.21/0.48  cnf(c_0_45, plain, (k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4))))=k2_zfmisc_1(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X4))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.48  cnf(c_0_46, negated_conjecture, (k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk2_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk2_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))))!=k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0)),k1_enumset1(esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.21/0.48  cnf(c_0_47, plain, (k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),k1_enumset1(k4_tarski(X4,X3),k4_tarski(k4_tarski(X1,X2),X5),k4_tarski(X4,X5))))=k2_zfmisc_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),X4),k1_enumset1(X3,X3,X5))), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 0.21/0.48  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_34])]), ['proof']).
% 0.21/0.48  # SZS output end CNFRefutation
% 0.21/0.48  # Proof object total steps             : 49
% 0.21/0.48  # Proof object clause steps            : 26
% 0.21/0.48  # Proof object formula steps           : 23
% 0.21/0.48  # Proof object conjectures             : 7
% 0.21/0.48  # Proof object clause conjectures      : 4
% 0.21/0.48  # Proof object formula conjectures     : 3
% 0.21/0.48  # Proof object initial clauses used    : 12
% 0.21/0.48  # Proof object initial formulas used   : 11
% 0.21/0.48  # Proof object generating inferences   : 3
% 0.21/0.48  # Proof object simplifying inferences  : 41
% 0.21/0.48  # Training examples: 0 positive, 0 negative
% 0.21/0.48  # Parsed axioms                        : 11
% 0.21/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.48  # Initial clauses                      : 12
% 0.21/0.48  # Removed in clause preprocessing      : 6
% 0.21/0.48  # Initial clauses in saturation        : 6
% 0.21/0.48  # Processed clauses                    : 1224
% 0.21/0.48  # ...of these trivial                  : 376
% 0.21/0.48  # ...subsumed                          : 642
% 0.21/0.48  # ...remaining for further processing  : 206
% 0.21/0.48  # Other redundant clauses eliminated   : 0
% 0.21/0.48  # Clauses deleted for lack of memory   : 0
% 0.21/0.48  # Backward-subsumed                    : 0
% 0.21/0.48  # Backward-rewritten                   : 3
% 0.21/0.48  # Generated clauses                    : 8839
% 0.21/0.48  # ...of the previous two non-trivial   : 3598
% 0.21/0.48  # Contextual simplify-reflections      : 0
% 0.21/0.48  # Paramodulations                      : 8839
% 0.21/0.48  # Factorizations                       : 0
% 0.21/0.48  # Equation resolutions                 : 0
% 0.21/0.48  # Propositional unsat checks           : 0
% 0.21/0.48  #    Propositional check models        : 0
% 0.21/0.48  #    Propositional check unsatisfiable : 0
% 0.21/0.48  #    Propositional clauses             : 0
% 0.21/0.48  #    Propositional clauses after purity: 0
% 0.21/0.48  #    Propositional unsat core size     : 0
% 0.21/0.48  #    Propositional preprocessing time  : 0.000
% 0.21/0.48  #    Propositional encoding time       : 0.000
% 0.21/0.48  #    Propositional solver time         : 0.000
% 0.21/0.48  #    Success case prop preproc time    : 0.000
% 0.21/0.48  #    Success case prop encoding time   : 0.000
% 0.21/0.48  #    Success case prop solver time     : 0.000
% 0.21/0.48  # Current number of processed clauses  : 197
% 0.21/0.48  #    Positive orientable unit clauses  : 195
% 0.21/0.48  #    Positive unorientable unit clauses: 2
% 0.21/0.48  #    Negative unit clauses             : 0
% 0.21/0.48  #    Non-unit-clauses                  : 0
% 0.21/0.48  # Current number of unprocessed clauses: 2374
% 0.21/0.48  # ...number of literals in the above   : 2374
% 0.21/0.48  # Current number of archived formulas  : 0
% 0.21/0.48  # Current number of archived clauses   : 15
% 0.21/0.48  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.48  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.48  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.48  # Unit Clause-clause subsumption calls : 5
% 0.21/0.48  # Rewrite failures with RHS unbound    : 0
% 0.21/0.48  # BW rewrite match attempts            : 10836
% 0.21/0.48  # BW rewrite match successes           : 67
% 0.21/0.48  # Condensation attempts                : 0
% 0.21/0.48  # Condensation successes               : 0
% 0.21/0.48  # Termbank termtop insertions          : 198530
% 0.21/0.48  
% 0.21/0.48  # -------------------------------------------------
% 0.21/0.48  # User time                : 0.130 s
% 0.21/0.48  # System time              : 0.004 s
% 0.21/0.48  # Total time               : 0.133 s
% 0.21/0.48  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
