%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   63 (1774 expanded)
%              Number of clauses        :   48 ( 768 expanded)
%              Number of leaves         :    7 ( 464 expanded)
%              Depth                    :   14
%              Number of atoms          :   77 (2706 expanded)
%              Number of equality atoms :   64 (2007 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_8,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_9,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk3_0,esk1_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & esk3_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X16,X17] : k2_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = X16 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_11,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_13,plain,(
    ! [X11,X12] : k4_xboole_0(k2_xboole_0(X11,X12),X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,esk1_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(esk2_0,esk4_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(esk1_0,esk3_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,esk2_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk1_0) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk2_0) = k4_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk1_0) = k4_xboole_0(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk4_0) = k4_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,X1)) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk1_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_34]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk2_0) = k4_xboole_0(k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),esk1_0) = k4_xboole_0(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk1_0) = k4_xboole_0(k1_xboole_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),esk4_0) = k4_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk2_0)) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_20]),c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,esk1_0)) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_40]),c_0_20])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_28]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(esk4_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_20]),c_0_23]),c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk1_0,X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(esk1_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_42]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(esk1_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_20])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk4_0,esk3_0),k3_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk2_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_44]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk4_0) = k4_xboole_0(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk1_0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23]),c_0_29]),c_0_23]),c_0_29]),c_0_47]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk4_0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_20]),c_0_48]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk4_0) = k4_xboole_0(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk1_0) = k4_xboole_0(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk1_0,esk4_0),k4_xboole_0(k1_xboole_0,esk4_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_58]),c_0_18]),c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_60]),c_0_34]),c_0_60]),c_0_21]),c_0_27]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.13/0.39  # and selection function SelectComplexG.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.026 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.13/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.39  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.13/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.39  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.13/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.13/0.39  fof(c_0_8, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.39  fof(c_0_9, negated_conjecture, (((k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)&r1_xboole_0(esk3_0,esk1_0))&r1_xboole_0(esk4_0,esk2_0))&esk3_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X16, X17]:k2_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,X17))=X16, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.13/0.39  fof(c_0_11, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.39  fof(c_0_12, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.39  fof(c_0_13, plain, ![X11, X12]:k4_xboole_0(k2_xboole_0(X11,X12),X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.13/0.39  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.39  cnf(c_0_17, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_21, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (k3_xboole_0(esk3_0,esk1_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.39  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_24, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_19])).
% 0.13/0.39  cnf(c_0_26, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_20])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,esk1_0))=esk3_0), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.13/0.39  cnf(c_0_28, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(esk2_0,esk4_0))=esk2_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(esk1_0,esk3_0))=esk1_0), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,esk2_0))=esk4_0), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk2_0,esk1_0)=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk2_0)=k4_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk1_0)=k4_xboole_0(X1,esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),esk4_0)=k4_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_32])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_23])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,X1))=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk1_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_34]), c_0_20])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk2_0,esk2_0)=k4_xboole_0(k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),esk1_0)=k4_xboole_0(X1,esk1_0)), inference(spm,[status(thm)],[c_0_36, c_0_23])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk1_0,esk1_0)=k4_xboole_0(k1_xboole_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_36])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),esk4_0)=k4_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_23])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk2_0))=k4_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_32]), c_0_20]), c_0_23])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,esk1_0))=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_23])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(k1_xboole_0,k2_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_40]), c_0_20])).
% 0.13/0.39  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_28]), c_0_20])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(esk4_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_20]), c_0_23]), c_0_29])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk1_0,X1))=k4_xboole_0(k1_xboole_0,k2_xboole_0(esk1_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_42]), c_0_20])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(esk1_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_31]), c_0_20])).
% 0.13/0.39  cnf(c_0_51, plain, (k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X3)),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk4_0,esk3_0),k3_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk2_0)))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_44]), c_0_23])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk4_0,esk4_0)=k4_xboole_0(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk4_0,esk1_0)=k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_23]), c_0_29]), c_0_23]), c_0_29]), c_0_47]), c_0_48])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk1_0,esk4_0)=k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_50])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k1_xboole_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_20]), c_0_48]), c_0_54])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk1_0,esk4_0)=k4_xboole_0(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk4_0,esk1_0)=k4_xboole_0(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[c_0_54, c_0_56])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (k2_xboole_0(k3_xboole_0(esk1_0,esk4_0),k4_xboole_0(k1_xboole_0,esk4_0))=esk1_0), inference(spm,[status(thm)],[c_0_17, c_0_57])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (esk4_0=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_58]), c_0_18]), c_0_59])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (esk3_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_60]), c_0_34]), c_0_60]), c_0_21]), c_0_27]), c_0_61]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 63
% 0.13/0.39  # Proof object clause steps            : 48
% 0.13/0.39  # Proof object formula steps           : 15
% 0.13/0.39  # Proof object conjectures             : 40
% 0.13/0.39  # Proof object clause conjectures      : 37
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 10
% 0.13/0.39  # Proof object initial formulas used   : 7
% 0.13/0.39  # Proof object generating inferences   : 35
% 0.13/0.39  # Proof object simplifying inferences  : 33
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 7
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 11
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 11
% 0.13/0.39  # Processed clauses                    : 216
% 0.13/0.39  # ...of these trivial                  : 51
% 0.13/0.39  # ...subsumed                          : 3
% 0.13/0.39  # ...remaining for further processing  : 162
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 102
% 0.13/0.39  # Generated clauses                    : 1483
% 0.13/0.39  # ...of the previous two non-trivial   : 1411
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 1483
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 60
% 0.13/0.39  #    Positive orientable unit clauses  : 54
% 0.13/0.39  #    Positive unorientable unit clauses: 2
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 3
% 0.13/0.39  # Current number of unprocessed clauses: 1149
% 0.13/0.39  # ...number of literals in the above   : 1149
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 102
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 7
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 7
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.39  # Unit Clause-clause subsumption calls : 1
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 47
% 0.13/0.39  # BW rewrite match successes           : 25
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 20727
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.047 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.052 s
% 0.13/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
