%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:43 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 398 expanded)
%              Number of clauses        :   26 ( 147 expanded)
%              Number of leaves         :   13 ( 125 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 400 expanded)
%              Number of equality atoms :   54 ( 399 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X12,X13,X14,X15,X16] : k3_enumset1(X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_21,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_17]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_17]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_17]),c_0_17]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

fof(c_0_34,plain,(
    ! [X29,X30,X31,X32] : k2_zfmisc_1(k2_tarski(X29,X30),k2_tarski(X31,X32)) = k2_enumset1(k4_tarski(X29,X31),k4_tarski(X29,X32),k4_tarski(X30,X31),k4_tarski(X30,X32)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X1,X2,X3,X3,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X2,X3,X3,X3) = k3_enumset1(X2,X2,X2,X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_30])).

fof(c_0_37,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

fof(c_0_38,plain,(
    ! [X36,X37,X38] : k3_mcart_1(X36,X37,X38) = k4_tarski(k4_tarski(X36,X37),X38) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_39,plain,(
    ! [X39,X40,X41] : k3_zfmisc_1(X39,X40,X41) = k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X2,X2,X2,X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_42,plain,(
    ! [X33,X34,X35] :
      ( k2_zfmisc_1(k1_tarski(X33),k2_tarski(X34,X35)) = k2_tarski(k4_tarski(X33,X34),k4_tarski(X33,X35))
      & k2_zfmisc_1(k2_tarski(X33,X34),k1_tarski(X35)) = k2_tarski(k4_tarski(X33,X35),k4_tarski(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_43,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)) = k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_17]),c_0_17]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X4,X3,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_41]),c_0_30])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_28]),c_0_17]),c_0_17]),c_0_17]),c_0_25]),c_0_25]),c_0_25]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_50,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4)) = k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X3),k3_enumset1(X2,X2,X2,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_28]),c_0_17]),c_0_17]),c_0_17]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.43/0.60  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.43/0.60  # and selection function SelectNewComplexAHP.
% 0.43/0.60  #
% 0.43/0.60  # Preprocessing time       : 0.026 s
% 0.43/0.60  # Presaturation interreduction done
% 0.43/0.60  
% 0.43/0.60  # Proof found!
% 0.43/0.60  # SZS status Theorem
% 0.43/0.60  # SZS output start CNFRefutation
% 0.43/0.60  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.43/0.60  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.43/0.60  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.43/0.60  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.43/0.60  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.43/0.60  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.43/0.60  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.43/0.60  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.43/0.60  fof(t44_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 0.43/0.60  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.43/0.60  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.43/0.60  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.43/0.60  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.43/0.60  fof(c_0_13, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.43/0.60  fof(c_0_14, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.43/0.60  fof(c_0_15, plain, ![X12, X13, X14, X15, X16]:k3_enumset1(X12,X13,X14,X15,X16)=k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.43/0.60  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.43/0.60  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  fof(c_0_18, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.43/0.60  fof(c_0_19, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.43/0.60  fof(c_0_20, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.43/0.60  fof(c_0_21, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.43/0.60  fof(c_0_22, plain, ![X6, X7]:k2_tarski(X6,X7)=k2_tarski(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.43/0.60  cnf(c_0_23, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.43/0.60  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.43/0.60  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.43/0.60  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.43/0.60  cnf(c_0_27, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.43/0.60  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.43/0.60  cnf(c_0_29, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.43/0.60  cnf(c_0_30, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_17]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.43/0.60  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_17]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.43/0.60  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_17]), c_0_17]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.43/0.60  fof(c_0_33, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5))), inference(assume_negation,[status(cth)],[t44_mcart_1])).
% 0.43/0.60  fof(c_0_34, plain, ![X29, X30, X31, X32]:k2_zfmisc_1(k2_tarski(X29,X30),k2_tarski(X31,X32))=k2_enumset1(k4_tarski(X29,X31),k4_tarski(X29,X32),k4_tarski(X30,X31),k4_tarski(X30,X32)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 0.43/0.60  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X1,X2,X3,X3,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.43/0.60  cnf(c_0_36, plain, (k3_enumset1(X1,X2,X3,X3,X3)=k3_enumset1(X2,X2,X2,X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_30])).
% 0.43/0.60  fof(c_0_37, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.43/0.60  fof(c_0_38, plain, ![X36, X37, X38]:k3_mcart_1(X36,X37,X38)=k4_tarski(k4_tarski(X36,X37),X38), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.43/0.60  fof(c_0_39, plain, ![X39, X40, X41]:k3_zfmisc_1(X39,X40,X41)=k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.43/0.60  cnf(c_0_40, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.43/0.60  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X2,X2,X2,X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.43/0.60  fof(c_0_42, plain, ![X33, X34, X35]:(k2_zfmisc_1(k1_tarski(X33),k2_tarski(X34,X35))=k2_tarski(k4_tarski(X33,X34),k4_tarski(X33,X35))&k2_zfmisc_1(k2_tarski(X33,X34),k1_tarski(X35))=k2_tarski(k4_tarski(X33,X35),k4_tarski(X34,X35))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.43/0.60  cnf(c_0_43, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.43/0.60  cnf(c_0_44, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.43/0.60  cnf(c_0_45, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.43/0.60  cnf(c_0_46, plain, (k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))=k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_17]), c_0_17]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26])).
% 0.43/0.60  cnf(c_0_47, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X4,X3,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_41]), c_0_30])).
% 0.43/0.60  cnf(c_0_48, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.43/0.60  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_28]), c_0_17]), c_0_17]), c_0_17]), c_0_25]), c_0_25]), c_0_25]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.43/0.60  cnf(c_0_50, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4))=k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X3),k3_enumset1(X2,X2,X2,X2,X4))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.43/0.60  cnf(c_0_51, plain, (k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))=k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_28]), c_0_17]), c_0_17]), c_0_17]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26])).
% 0.43/0.60  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), ['proof']).
% 0.43/0.60  # SZS output end CNFRefutation
% 0.43/0.60  # Proof object total steps             : 53
% 0.43/0.60  # Proof object clause steps            : 26
% 0.43/0.60  # Proof object formula steps           : 27
% 0.43/0.60  # Proof object conjectures             : 6
% 0.43/0.60  # Proof object clause conjectures      : 3
% 0.43/0.60  # Proof object formula conjectures     : 3
% 0.43/0.60  # Proof object initial clauses used    : 13
% 0.43/0.60  # Proof object initial formulas used   : 13
% 0.43/0.60  # Proof object generating inferences   : 5
% 0.43/0.60  # Proof object simplifying inferences  : 69
% 0.43/0.60  # Training examples: 0 positive, 0 negative
% 0.43/0.60  # Parsed axioms                        : 13
% 0.43/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.60  # Initial clauses                      : 14
% 0.43/0.60  # Removed in clause preprocessing      : 7
% 0.43/0.60  # Initial clauses in saturation        : 7
% 0.43/0.60  # Processed clauses                    : 6749
% 0.43/0.60  # ...of these trivial                  : 12
% 0.43/0.60  # ...subsumed                          : 6539
% 0.43/0.60  # ...remaining for further processing  : 198
% 0.43/0.60  # Other redundant clauses eliminated   : 0
% 0.43/0.60  # Clauses deleted for lack of memory   : 0
% 0.43/0.60  # Backward-subsumed                    : 11
% 0.43/0.60  # Backward-rewritten                   : 4
% 0.43/0.60  # Generated clauses                    : 51190
% 0.43/0.60  # ...of the previous two non-trivial   : 45185
% 0.43/0.60  # Contextual simplify-reflections      : 0
% 0.43/0.60  # Paramodulations                      : 51190
% 0.43/0.60  # Factorizations                       : 0
% 0.43/0.60  # Equation resolutions                 : 0
% 0.43/0.60  # Propositional unsat checks           : 0
% 0.43/0.60  #    Propositional check models        : 0
% 0.43/0.60  #    Propositional check unsatisfiable : 0
% 0.43/0.60  #    Propositional clauses             : 0
% 0.43/0.60  #    Propositional clauses after purity: 0
% 0.43/0.60  #    Propositional unsat core size     : 0
% 0.43/0.60  #    Propositional preprocessing time  : 0.000
% 0.43/0.60  #    Propositional encoding time       : 0.000
% 0.43/0.60  #    Propositional solver time         : 0.000
% 0.43/0.60  #    Success case prop preproc time    : 0.000
% 0.43/0.60  #    Success case prop encoding time   : 0.000
% 0.43/0.60  #    Success case prop solver time     : 0.000
% 0.43/0.60  # Current number of processed clauses  : 176
% 0.43/0.60  #    Positive orientable unit clauses  : 16
% 0.43/0.60  #    Positive unorientable unit clauses: 160
% 0.43/0.60  #    Negative unit clauses             : 0
% 0.43/0.60  #    Non-unit-clauses                  : 0
% 0.43/0.60  # Current number of unprocessed clauses: 38022
% 0.43/0.60  # ...number of literals in the above   : 38022
% 0.43/0.60  # Current number of archived formulas  : 0
% 0.43/0.60  # Current number of archived clauses   : 29
% 0.43/0.60  # Clause-clause subsumption calls (NU) : 0
% 0.43/0.60  # Rec. Clause-clause subsumption calls : 0
% 0.43/0.60  # Non-unit clause-clause subsumptions  : 0
% 0.43/0.60  # Unit Clause-clause subsumption calls : 14160
% 0.43/0.60  # Rewrite failures with RHS unbound    : 0
% 0.43/0.60  # BW rewrite match attempts            : 23577
% 0.43/0.60  # BW rewrite match successes           : 6572
% 0.43/0.60  # Condensation attempts                : 0
% 0.43/0.60  # Condensation successes               : 0
% 0.43/0.60  # Termbank termtop insertions          : 207537
% 0.43/0.61  
% 0.43/0.61  # -------------------------------------------------
% 0.43/0.61  # User time                : 0.247 s
% 0.43/0.61  # System time              : 0.014 s
% 0.43/0.61  # Total time               : 0.261 s
% 0.43/0.61  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
