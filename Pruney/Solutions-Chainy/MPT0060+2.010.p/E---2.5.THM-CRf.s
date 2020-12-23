%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:25 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 (1363 expanded)
%              Number of clauses        :   51 ( 638 expanded)
%              Number of leaves         :    9 ( 362 expanded)
%              Depth                    :   14
%              Number of atoms          :   79 (1859 expanded)
%              Number of equality atoms :   56 (1056 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t53_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_10,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( k4_xboole_0(X4,X5) != k1_xboole_0
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | k4_xboole_0(X4,X5) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_19])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] : k3_xboole_0(X18,k4_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_33,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_28]),c_0_26])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_28]),c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_43])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_22])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t53_xboole_1])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) = k2_xboole_0(k2_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_37])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_47])).

fof(c_0_53,negated_conjecture,(
    k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,X3)),X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_36])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_52]),c_0_36]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_22])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_58])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_22])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))))) != k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_22]),c_0_22])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_62]),c_0_62])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_22]),c_0_38]),c_0_22]),c_0_47])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))) = k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),c_0_67]),c_0_22]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:12:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.51  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.22/0.51  # and selection function SelectNewComplexAHP.
% 0.22/0.51  #
% 0.22/0.51  # Preprocessing time       : 0.026 s
% 0.22/0.51  # Presaturation interreduction done
% 0.22/0.51  
% 0.22/0.51  # Proof found!
% 0.22/0.51  # SZS status Theorem
% 0.22/0.51  # SZS output start CNFRefutation
% 0.22/0.51  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.22/0.51  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.22/0.51  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.22/0.51  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.22/0.51  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.22/0.51  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.22/0.51  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.22/0.51  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.22/0.51  fof(t53_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 0.22/0.51  fof(c_0_9, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.22/0.51  fof(c_0_10, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.22/0.51  fof(c_0_11, plain, ![X4, X5]:((k4_xboole_0(X4,X5)!=k1_xboole_0|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|k4_xboole_0(X4,X5)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.22/0.51  fof(c_0_12, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.22/0.51  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.51  cnf(c_0_14, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.51  fof(c_0_15, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.22/0.51  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.51  cnf(c_0_17, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.51  fof(c_0_18, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.22/0.51  cnf(c_0_19, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.22/0.51  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.51  cnf(c_0_21, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.22/0.51  cnf(c_0_22, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.51  cnf(c_0_23, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_19])).
% 0.22/0.51  cnf(c_0_24, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_13, c_0_17])).
% 0.22/0.51  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.22/0.51  cnf(c_0_26, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.22/0.51  cnf(c_0_27, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.51  cnf(c_0_28, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.22/0.51  cnf(c_0_29, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.22/0.51  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_25]), c_0_26])).
% 0.22/0.51  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.22/0.51  fof(c_0_32, plain, ![X18, X19, X20]:k3_xboole_0(X18,k4_xboole_0(X19,X20))=k4_xboole_0(k3_xboole_0(X18,X19),X20), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.22/0.51  fof(c_0_33, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.22/0.51  cnf(c_0_34, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 0.22/0.51  cnf(c_0_35, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_28]), c_0_26])).
% 0.22/0.51  cnf(c_0_36, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_28]), c_0_29])).
% 0.22/0.51  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.22/0.51  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_31])).
% 0.22/0.51  cnf(c_0_39, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.22/0.51  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.22/0.51  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 0.22/0.51  cnf(c_0_42, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_35]), c_0_36])).
% 0.22/0.51  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.22/0.51  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_40])).
% 0.22/0.51  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.22/0.51  cnf(c_0_46, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_13, c_0_43])).
% 0.22/0.51  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_44, c_0_22])).
% 0.22/0.51  fof(c_0_48, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t53_xboole_1])).
% 0.22/0.51  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.22/0.51  cnf(c_0_50, plain, (k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))=k2_xboole_0(k2_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_13, c_0_37])).
% 0.22/0.51  cnf(c_0_51, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.22/0.51  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_47])).
% 0.22/0.51  fof(c_0_53, negated_conjecture, k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 0.22/0.51  cnf(c_0_54, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,X3)),X3))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.22/0.51  cnf(c_0_55, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_36])).
% 0.22/0.51  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_52]), c_0_36]), c_0_24])).
% 0.22/0.51  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.22/0.51  cnf(c_0_58, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.22/0.51  cnf(c_0_59, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_56, c_0_22])).
% 0.22/0.51  cnf(c_0_60, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_42, c_0_24])).
% 0.22/0.51  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_57, c_0_40])).
% 0.22/0.51  cnf(c_0_62, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_58])).
% 0.22/0.51  cnf(c_0_63, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_22])).
% 0.22/0.51  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_19])).
% 0.22/0.51  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)))))!=k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_22]), c_0_22])).
% 0.22/0.51  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_62]), c_0_62])).
% 0.22/0.51  cnf(c_0_67, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_22]), c_0_38]), c_0_22]), c_0_47])).
% 0.22/0.51  cnf(c_0_68, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))=k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_51, c_0_47])).
% 0.22/0.51  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), c_0_67]), c_0_22]), c_0_64])]), ['proof']).
% 0.22/0.51  # SZS output end CNFRefutation
% 0.22/0.51  # Proof object total steps             : 70
% 0.22/0.51  # Proof object clause steps            : 51
% 0.22/0.51  # Proof object formula steps           : 19
% 0.22/0.51  # Proof object conjectures             : 7
% 0.22/0.51  # Proof object clause conjectures      : 4
% 0.22/0.51  # Proof object formula conjectures     : 3
% 0.22/0.51  # Proof object initial clauses used    : 10
% 0.22/0.51  # Proof object initial formulas used   : 9
% 0.22/0.51  # Proof object generating inferences   : 35
% 0.22/0.51  # Proof object simplifying inferences  : 29
% 0.22/0.51  # Training examples: 0 positive, 0 negative
% 0.22/0.51  # Parsed axioms                        : 9
% 0.22/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.51  # Initial clauses                      : 10
% 0.22/0.51  # Removed in clause preprocessing      : 1
% 0.22/0.51  # Initial clauses in saturation        : 9
% 0.22/0.51  # Processed clauses                    : 820
% 0.22/0.51  # ...of these trivial                  : 291
% 0.22/0.51  # ...subsumed                          : 285
% 0.22/0.51  # ...remaining for further processing  : 243
% 0.22/0.51  # Other redundant clauses eliminated   : 0
% 0.22/0.51  # Clauses deleted for lack of memory   : 0
% 0.22/0.51  # Backward-subsumed                    : 0
% 0.22/0.51  # Backward-rewritten                   : 113
% 0.22/0.51  # Generated clauses                    : 18706
% 0.22/0.51  # ...of the previous two non-trivial   : 8856
% 0.22/0.51  # Contextual simplify-reflections      : 0
% 0.22/0.51  # Paramodulations                      : 18700
% 0.22/0.51  # Factorizations                       : 0
% 0.22/0.51  # Equation resolutions                 : 6
% 0.22/0.51  # Propositional unsat checks           : 0
% 0.22/0.51  #    Propositional check models        : 0
% 0.22/0.51  #    Propositional check unsatisfiable : 0
% 0.22/0.51  #    Propositional clauses             : 0
% 0.22/0.51  #    Propositional clauses after purity: 0
% 0.22/0.51  #    Propositional unsat core size     : 0
% 0.22/0.51  #    Propositional preprocessing time  : 0.000
% 0.22/0.51  #    Propositional encoding time       : 0.000
% 0.22/0.51  #    Propositional solver time         : 0.000
% 0.22/0.51  #    Success case prop preproc time    : 0.000
% 0.22/0.51  #    Success case prop encoding time   : 0.000
% 0.22/0.51  #    Success case prop solver time     : 0.000
% 0.22/0.51  # Current number of processed clauses  : 121
% 0.22/0.51  #    Positive orientable unit clauses  : 102
% 0.22/0.51  #    Positive unorientable unit clauses: 4
% 0.22/0.51  #    Negative unit clauses             : 0
% 0.22/0.51  #    Non-unit-clauses                  : 15
% 0.22/0.51  # Current number of unprocessed clauses: 7626
% 0.22/0.51  # ...number of literals in the above   : 7902
% 0.22/0.51  # Current number of archived formulas  : 0
% 0.22/0.51  # Current number of archived clauses   : 123
% 0.22/0.51  # Clause-clause subsumption calls (NU) : 205
% 0.22/0.51  # Rec. Clause-clause subsumption calls : 205
% 0.22/0.51  # Non-unit clause-clause subsumptions  : 76
% 0.22/0.51  # Unit Clause-clause subsumption calls : 73
% 0.22/0.51  # Rewrite failures with RHS unbound    : 0
% 0.22/0.51  # BW rewrite match attempts            : 804
% 0.22/0.51  # BW rewrite match successes           : 364
% 0.22/0.51  # Condensation attempts                : 0
% 0.22/0.51  # Condensation successes               : 0
% 0.22/0.51  # Termbank termtop insertions          : 141884
% 0.22/0.51  
% 0.22/0.51  # -------------------------------------------------
% 0.22/0.51  # User time                : 0.144 s
% 0.22/0.51  # System time              : 0.008 s
% 0.22/0.51  # Total time               : 0.153 s
% 0.22/0.51  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
