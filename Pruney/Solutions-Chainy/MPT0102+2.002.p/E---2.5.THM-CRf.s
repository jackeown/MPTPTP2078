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
% DateTime   : Thu Dec  3 10:34:01 EST 2020

% Result     : Theorem 10.52s
% Output     : CNFRefutation 10.52s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 227 expanded)
%              Number of clauses        :   32 (  98 expanded)
%              Number of leaves         :   12 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 257 expanded)
%              Number of equality atoms :   52 ( 209 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(c_0_12,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_13,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_15,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_19,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

fof(c_0_23,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k2_xboole_0(X19,X20),X21) = k2_xboole_0(k4_xboole_0(X19,X21),k4_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,X12) != k1_xboole_0
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | k4_xboole_0(X11,X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_30,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_31,negated_conjecture,(
    k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_32,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_17]),c_0_17])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_20])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_17]),c_0_41]),c_0_41])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_26])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0))) != k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_21]),c_0_21]),c_0_21]),c_0_21]),c_0_21]),c_0_42])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_48])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k2_xboole_0(X1,X4)) = k4_xboole_0(X3,k2_xboole_0(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_29])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_51]),c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_42]),c_0_54]),c_0_39]),c_0_55]),c_0_44]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:01:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 10.52/10.72  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 10.52/10.72  # and selection function SelectNewComplexAHP.
% 10.52/10.72  #
% 10.52/10.72  # Preprocessing time       : 0.026 s
% 10.52/10.72  # Presaturation interreduction done
% 10.52/10.72  
% 10.52/10.72  # Proof found!
% 10.52/10.72  # SZS status Theorem
% 10.52/10.72  # SZS output start CNFRefutation
% 10.52/10.72  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 10.52/10.72  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.52/10.72  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.52/10.72  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.52/10.72  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.52/10.72  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.52/10.72  fof(t95_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.52/10.72  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.52/10.72  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 10.52/10.72  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.52/10.72  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.52/10.72  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 10.52/10.72  fof(c_0_12, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 10.52/10.72  fof(c_0_13, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 10.52/10.72  fof(c_0_14, plain, ![X13]:k2_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t1_boole])).
% 10.52/10.72  fof(c_0_15, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 10.52/10.72  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 10.52/10.72  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.52/10.72  fof(c_0_18, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 10.52/10.72  fof(c_0_19, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 10.52/10.72  cnf(c_0_20, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 10.52/10.72  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.52/10.72  fof(c_0_22, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t95_xboole_1])).
% 10.52/10.72  fof(c_0_23, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 10.52/10.72  fof(c_0_24, plain, ![X19, X20, X21]:k4_xboole_0(k2_xboole_0(X19,X20),X21)=k2_xboole_0(k4_xboole_0(X19,X21),k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 10.52/10.72  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 10.52/10.72  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 10.52/10.72  fof(c_0_27, plain, ![X11, X12]:((k4_xboole_0(X11,X12)!=k1_xboole_0|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|k4_xboole_0(X11,X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 10.52/10.72  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.52/10.72  cnf(c_0_29, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 10.52/10.72  fof(c_0_30, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 10.52/10.72  fof(c_0_31, negated_conjecture, k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 10.52/10.72  fof(c_0_32, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 10.52/10.72  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 10.52/10.72  cnf(c_0_34, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 10.52/10.72  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 10.52/10.72  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.52/10.72  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 10.52/10.72  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 10.52/10.72  cnf(c_0_39, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.52/10.72  cnf(c_0_40, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 10.52/10.72  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 10.52/10.72  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_17]), c_0_17])).
% 10.52/10.72  cnf(c_0_43, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_20])).
% 10.52/10.72  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 10.52/10.72  cnf(c_0_45, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_38])).
% 10.52/10.72  cnf(c_0_46, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_39]), c_0_39]), c_0_39])).
% 10.52/10.72  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_17]), c_0_41]), c_0_41])).
% 10.52/10.72  cnf(c_0_48, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_26])).
% 10.52/10.72  cnf(c_0_49, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3))=k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3)), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 10.52/10.72  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_44]), c_0_45]), c_0_46])).
% 10.52/10.72  cnf(c_0_51, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 10.52/10.72  cnf(c_0_52, negated_conjecture, (k2_xboole_0(k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk2_0,esk1_0)))!=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_21]), c_0_21]), c_0_21]), c_0_21]), c_0_21]), c_0_42])).
% 10.52/10.72  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_39, c_0_48])).
% 10.52/10.72  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k2_xboole_0(X1,X4))=k4_xboole_0(X3,k2_xboole_0(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_29])).
% 10.52/10.72  cnf(c_0_55, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_51]), c_0_26])).
% 10.52/10.72  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_42]), c_0_54]), c_0_39]), c_0_55]), c_0_44]), c_0_20])]), ['proof']).
% 10.52/10.72  # SZS output end CNFRefutation
% 10.52/10.72  # Proof object total steps             : 57
% 10.52/10.72  # Proof object clause steps            : 32
% 10.52/10.72  # Proof object formula steps           : 25
% 10.52/10.72  # Proof object conjectures             : 7
% 10.52/10.72  # Proof object clause conjectures      : 4
% 10.52/10.72  # Proof object formula conjectures     : 3
% 10.52/10.72  # Proof object initial clauses used    : 12
% 10.52/10.72  # Proof object initial formulas used   : 12
% 10.52/10.72  # Proof object generating inferences   : 14
% 10.52/10.72  # Proof object simplifying inferences  : 30
% 10.52/10.72  # Training examples: 0 positive, 0 negative
% 10.52/10.72  # Parsed axioms                        : 13
% 10.52/10.72  # Removed by relevancy pruning/SinE    : 0
% 10.52/10.72  # Initial clauses                      : 14
% 10.52/10.72  # Removed in clause preprocessing      : 2
% 10.52/10.72  # Initial clauses in saturation        : 12
% 10.52/10.72  # Processed clauses                    : 16952
% 10.52/10.72  # ...of these trivial                  : 8283
% 10.52/10.72  # ...subsumed                          : 7010
% 10.52/10.72  # ...remaining for further processing  : 1658
% 10.52/10.72  # Other redundant clauses eliminated   : 0
% 10.52/10.72  # Clauses deleted for lack of memory   : 0
% 10.52/10.72  # Backward-subsumed                    : 1
% 10.52/10.72  # Backward-rewritten                   : 338
% 10.52/10.72  # Generated clauses                    : 1180683
% 10.52/10.72  # ...of the previous two non-trivial   : 878345
% 10.52/10.72  # Contextual simplify-reflections      : 0
% 10.52/10.72  # Paramodulations                      : 1180658
% 10.52/10.72  # Factorizations                       : 0
% 10.52/10.72  # Equation resolutions                 : 25
% 10.52/10.72  # Propositional unsat checks           : 0
% 10.52/10.72  #    Propositional check models        : 0
% 10.52/10.72  #    Propositional check unsatisfiable : 0
% 10.52/10.72  #    Propositional clauses             : 0
% 10.52/10.72  #    Propositional clauses after purity: 0
% 10.52/10.72  #    Propositional unsat core size     : 0
% 10.52/10.72  #    Propositional preprocessing time  : 0.000
% 10.52/10.72  #    Propositional encoding time       : 0.000
% 10.52/10.72  #    Propositional solver time         : 0.000
% 10.52/10.72  #    Success case prop preproc time    : 0.000
% 10.52/10.72  #    Success case prop encoding time   : 0.000
% 10.52/10.72  #    Success case prop solver time     : 0.000
% 10.52/10.72  # Current number of processed clauses  : 1307
% 10.52/10.72  #    Positive orientable unit clauses  : 1107
% 10.52/10.72  #    Positive unorientable unit clauses: 32
% 10.52/10.72  #    Negative unit clauses             : 0
% 10.52/10.72  #    Non-unit-clauses                  : 168
% 10.52/10.72  # Current number of unprocessed clauses: 853890
% 10.52/10.72  # ...number of literals in the above   : 913220
% 10.52/10.72  # Current number of archived formulas  : 0
% 10.52/10.72  # Current number of archived clauses   : 353
% 10.52/10.72  # Clause-clause subsumption calls (NU) : 36296
% 10.52/10.72  # Rec. Clause-clause subsumption calls : 36296
% 10.52/10.72  # Non-unit clause-clause subsumptions  : 2791
% 10.52/10.72  # Unit Clause-clause subsumption calls : 707
% 10.52/10.72  # Rewrite failures with RHS unbound    : 0
% 10.52/10.72  # BW rewrite match attempts            : 24665
% 10.52/10.72  # BW rewrite match successes           : 1143
% 10.52/10.72  # Condensation attempts                : 0
% 10.52/10.72  # Condensation successes               : 0
% 10.52/10.72  # Termbank termtop insertions          : 16396442
% 10.52/10.76  
% 10.52/10.76  # -------------------------------------------------
% 10.52/10.76  # User time                : 9.995 s
% 10.52/10.76  # System time              : 0.428 s
% 10.52/10.76  # Total time               : 10.423 s
% 10.52/10.76  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
