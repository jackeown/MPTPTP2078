%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 145 expanded)
%              Number of clauses        :   25 (  60 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 149 expanded)
%              Number of equality atoms :   44 ( 141 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t87_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

fof(c_0_12,negated_conjecture,(
    k2_xboole_0(esk2_0,esk3_0) != k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_15,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) != k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] : k2_xboole_0(k2_xboole_0(X23,X24),X25) = k2_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_23,plain,(
    ! [X8] : k2_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_24,plain,(
    ! [X26,X27] : k2_xboole_0(k3_xboole_0(X26,X27),k4_xboole_0(X26,X27)) = X26 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_25,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X16,X15)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_xboole_0(X32,X33)
      | k2_xboole_0(k4_xboole_0(X34,X32),X33) = k4_xboole_0(k2_xboole_0(X34,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_16])).

fof(c_0_37,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2)))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_28])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X2,X3),X1)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_20]),c_0_32]),c_0_20])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_28])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_28])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_27]),c_0_42]),c_0_20]),c_0_43])]),c_0_44]),c_0_20]),c_0_45]),c_0_39]),c_0_46]),c_0_20]),c_0_32]),c_0_44]),c_0_20]),c_0_42]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t94_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.20/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.41  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.20/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.41  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.41  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.41  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.41  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.41  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.41  fof(t87_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 0.20/0.41  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.41  fof(c_0_11, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t94_xboole_1])).
% 0.20/0.41  fof(c_0_12, negated_conjecture, k2_xboole_0(esk2_0,esk3_0)!=k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.41  fof(c_0_13, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.41  fof(c_0_14, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.20/0.41  cnf(c_0_15, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)!=k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_17, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_18, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_17])).
% 0.20/0.41  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_21, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.41  fof(c_0_22, plain, ![X23, X24, X25]:k2_xboole_0(k2_xboole_0(X23,X24),X25)=k2_xboole_0(X23,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.41  fof(c_0_23, plain, ![X8]:k2_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.41  fof(c_0_24, plain, ![X26, X27]:k2_xboole_0(k3_xboole_0(X26,X27),k4_xboole_0(X26,X27))=X26, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.41  fof(c_0_25, plain, ![X15, X16]:k2_xboole_0(X15,k4_xboole_0(X16,X15))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))!=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.41  cnf(c_0_27, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_28, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_29, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  fof(c_0_30, plain, ![X32, X33, X34]:(~r1_xboole_0(X32,X33)|k2_xboole_0(k4_xboole_0(X34,X32),X33)=k4_xboole_0(k2_xboole_0(X34,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).
% 0.20/0.41  cnf(c_0_31, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))!=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_34, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_35, plain, (k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_36, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_31, c_0_16])).
% 0.20/0.41  fof(c_0_37, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.41  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2))))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_28])).
% 0.20/0.41  cnf(c_0_39, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_32, c_0_27])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))!=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.41  cnf(c_0_41, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X2,X3),X1)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 0.20/0.41  cnf(c_0_42, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_20]), c_0_32]), c_0_20])).
% 0.20/0.41  cnf(c_0_43, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_44, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_28])).
% 0.20/0.41  cnf(c_0_45, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_28])).
% 0.20/0.41  cnf(c_0_46, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_27]), c_0_42]), c_0_20]), c_0_43])]), c_0_44]), c_0_20]), c_0_45]), c_0_39]), c_0_46]), c_0_20]), c_0_32]), c_0_44]), c_0_20]), c_0_42]), c_0_20])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 48
% 0.20/0.41  # Proof object clause steps            : 25
% 0.20/0.41  # Proof object formula steps           : 23
% 0.20/0.41  # Proof object conjectures             : 9
% 0.20/0.41  # Proof object clause conjectures      : 6
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 11
% 0.20/0.41  # Proof object initial formulas used   : 11
% 0.20/0.41  # Proof object generating inferences   : 7
% 0.20/0.41  # Proof object simplifying inferences  : 30
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 15
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 17
% 0.20/0.41  # Removed in clause preprocessing      : 2
% 0.20/0.41  # Initial clauses in saturation        : 15
% 0.20/0.41  # Processed clauses                    : 497
% 0.20/0.41  # ...of these trivial                  : 22
% 0.20/0.41  # ...subsumed                          : 343
% 0.20/0.41  # ...remaining for further processing  : 131
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 3
% 0.20/0.41  # Backward-rewritten                   : 9
% 0.20/0.41  # Generated clauses                    : 3107
% 0.20/0.41  # ...of the previous two non-trivial   : 2494
% 0.20/0.41  # Contextual simplify-reflections      : 1
% 0.20/0.41  # Paramodulations                      : 3107
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 104
% 0.20/0.41  #    Positive orientable unit clauses  : 33
% 0.20/0.41  #    Positive unorientable unit clauses: 3
% 0.20/0.41  #    Negative unit clauses             : 7
% 0.20/0.41  #    Non-unit-clauses                  : 61
% 0.20/0.41  # Current number of unprocessed clauses: 2017
% 0.20/0.41  # ...number of literals in the above   : 4459
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 29
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1183
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1090
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 194
% 0.20/0.41  # Unit Clause-clause subsumption calls : 72
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 129
% 0.20/0.41  # BW rewrite match successes           : 52
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 30947
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.067 s
% 0.20/0.41  # System time              : 0.004 s
% 0.20/0.41  # Total time               : 0.070 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
