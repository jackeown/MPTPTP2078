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
% DateTime   : Thu Dec  3 10:34:58 EST 2020

% Result     : Theorem 10.25s
% Output     : CNFRefutation 10.25s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 139 expanded)
%              Number of clauses        :   33 (  61 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 211 expanded)
%              Number of equality atoms :   35 ( 107 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X4)
        & r1_xboole_0(X2,X4)
        & r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_xboole_0(X1,X4)
          & r1_xboole_0(X2,X4)
          & r1_xboole_0(X3,X4) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    inference(assume_negation,[status(cth)],[t114_xboole_1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X14,k2_xboole_0(X15,X16)) = k3_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X16)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

fof(c_0_11,plain,(
    ! [X22,X23] : k2_xboole_0(X22,X23) = k5_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0)
    & r1_xboole_0(esk2_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_15,plain,(
    ! [X17,X18] :
      ( ( ~ r1_xboole_0(X17,X18)
        | k4_xboole_0(X17,X18) = X17 )
      & ( k4_xboole_0(X17,X18) != X17
        | r1_xboole_0(X17,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X7,X8] : k4_xboole_0(X7,k3_xboole_0(X7,X8)) = k4_xboole_0(X7,X8) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X11,X12,X13] : k2_xboole_0(k2_xboole_0(X11,X12),X13) = k2_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) != X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk1_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X19,X20,X21] : k5_xboole_0(k5_xboole_0(X19,X20),X21) = k5_xboole_0(X19,k5_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(X1,esk1_0)))
    | k4_xboole_0(esk4_0,X1) != esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),esk1_0)))
    | k4_xboole_0(k4_xboole_0(esk4_0,X1),k4_xboole_0(k4_xboole_0(esk4_0,X1),k4_xboole_0(esk4_0,X2))) != esk4_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk3_0,k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_17]),c_0_17])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(X1,esk2_0)),esk1_0)))
    | k4_xboole_0(esk4_0,X1) != esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk1_0,k5_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(k4_xboole_0(esk3_0,esk1_0),k4_xboole_0(k4_xboole_0(esk3_0,esk1_0),k4_xboole_0(esk3_0,esk2_0))))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_39]),c_0_23])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(X3,X2))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 10.25/10.43  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 10.25/10.43  # and selection function SelectComplexG.
% 10.25/10.43  #
% 10.25/10.43  # Preprocessing time       : 0.026 s
% 10.25/10.43  
% 10.25/10.43  # Proof found!
% 10.25/10.43  # SZS status Theorem
% 10.25/10.43  # SZS output start CNFRefutation
% 10.25/10.43  fof(t114_xboole_1, conjecture, ![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 10.25/10.43  fof(t53_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 10.25/10.43  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.25/10.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.25/10.43  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.25/10.43  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.25/10.43  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.25/10.43  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 10.25/10.43  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.25/10.43  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4))), inference(assume_negation,[status(cth)],[t114_xboole_1])).
% 10.25/10.43  fof(c_0_10, plain, ![X14, X15, X16]:k4_xboole_0(X14,k2_xboole_0(X15,X16))=k3_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[t53_xboole_1])).
% 10.25/10.43  fof(c_0_11, plain, ![X22, X23]:k2_xboole_0(X22,X23)=k5_xboole_0(X22,k4_xboole_0(X23,X22)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 10.25/10.43  fof(c_0_12, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 10.25/10.43  fof(c_0_13, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 10.25/10.43  fof(c_0_14, negated_conjecture, (((r1_xboole_0(esk1_0,esk4_0)&r1_xboole_0(esk2_0,esk4_0))&r1_xboole_0(esk3_0,esk4_0))&~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 10.25/10.43  fof(c_0_15, plain, ![X17, X18]:((~r1_xboole_0(X17,X18)|k4_xboole_0(X17,X18)=X17)&(k4_xboole_0(X17,X18)!=X17|r1_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 10.25/10.43  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 10.25/10.43  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 10.25/10.43  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 10.25/10.43  cnf(c_0_19, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.25/10.43  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 10.25/10.43  fof(c_0_21, plain, ![X7, X8]:k4_xboole_0(X7,k3_xboole_0(X7,X8))=k4_xboole_0(X7,X8), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 10.25/10.43  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.25/10.43  cnf(c_0_23, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 10.25/10.43  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 10.25/10.43  cnf(c_0_25, negated_conjecture, (r1_xboole_0(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 10.25/10.43  cnf(c_0_26, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 10.25/10.43  fof(c_0_27, plain, ![X11, X12, X13]:k2_xboole_0(k2_xboole_0(X11,X12),X13)=k2_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 10.25/10.43  cnf(c_0_28, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))|k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))!=X1), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 10.25/10.43  cnf(c_0_29, negated_conjecture, (k4_xboole_0(esk4_0,esk1_0)=esk4_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 10.25/10.43  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_18])).
% 10.25/10.43  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 10.25/10.43  cnf(c_0_32, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.25/10.43  fof(c_0_33, plain, ![X19, X20, X21]:k5_xboole_0(k5_xboole_0(X19,X20),X21)=k5_xboole_0(X19,k5_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 10.25/10.43  cnf(c_0_34, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(X1,esk1_0)))|k4_xboole_0(esk4_0,X1)!=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 10.25/10.43  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_31])).
% 10.25/10.43  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 10.25/10.43  cnf(c_0_37, negated_conjecture, (~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 10.25/10.43  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 10.25/10.43  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 10.25/10.43  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),esk1_0)))|k4_xboole_0(k4_xboole_0(esk4_0,X1),k4_xboole_0(k4_xboole_0(esk4_0,X1),k4_xboole_0(esk4_0,X2)))!=esk4_0), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 10.25/10.43  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_24, c_0_35])).
% 10.25/10.43  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_36])).
% 10.25/10.43  cnf(c_0_43, negated_conjecture, (~r1_xboole_0(k5_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk3_0,k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_17]), c_0_17])).
% 10.25/10.43  cnf(c_0_44, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 10.25/10.43  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(X1,esk2_0)),esk1_0)))|k4_xboole_0(esk4_0,X1)!=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_30])).
% 10.25/10.43  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_24, c_0_42])).
% 10.25/10.43  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk1_0,k5_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(k4_xboole_0(esk3_0,esk1_0),k4_xboole_0(k4_xboole_0(esk3_0,esk1_0),k4_xboole_0(esk3_0,esk2_0))))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_39]), c_0_23])).
% 10.25/10.43  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(k4_xboole_0(X3,X1),k4_xboole_0(X3,X2)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 10.25/10.43  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 10.25/10.43  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk1_0,k4_xboole_0(k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),esk1_0)),esk4_0)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 10.25/10.43  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_49]), c_0_50]), ['proof']).
% 10.25/10.43  # SZS output end CNFRefutation
% 10.25/10.43  # Proof object total steps             : 52
% 10.25/10.43  # Proof object clause steps            : 33
% 10.25/10.43  # Proof object formula steps           : 19
% 10.25/10.43  # Proof object conjectures             : 21
% 10.25/10.43  # Proof object clause conjectures      : 18
% 10.25/10.43  # Proof object formula conjectures     : 3
% 10.25/10.43  # Proof object initial clauses used    : 13
% 10.25/10.43  # Proof object initial formulas used   : 9
% 10.25/10.43  # Proof object generating inferences   : 13
% 10.25/10.43  # Proof object simplifying inferences  : 16
% 10.25/10.43  # Training examples: 0 positive, 0 negative
% 10.25/10.43  # Parsed axioms                        : 9
% 10.25/10.43  # Removed by relevancy pruning/SinE    : 0
% 10.25/10.43  # Initial clauses                      : 13
% 10.25/10.43  # Removed in clause preprocessing      : 2
% 10.25/10.43  # Initial clauses in saturation        : 11
% 10.25/10.43  # Processed clauses                    : 4780
% 10.25/10.43  # ...of these trivial                  : 526
% 10.25/10.43  # ...subsumed                          : 1986
% 10.25/10.43  # ...remaining for further processing  : 2268
% 10.25/10.43  # Other redundant clauses eliminated   : 0
% 10.25/10.43  # Clauses deleted for lack of memory   : 0
% 10.25/10.43  # Backward-subsumed                    : 6
% 10.25/10.43  # Backward-rewritten                   : 328
% 10.25/10.43  # Generated clauses                    : 561384
% 10.25/10.43  # ...of the previous two non-trivial   : 534511
% 10.25/10.43  # Contextual simplify-reflections      : 0
% 10.25/10.43  # Paramodulations                      : 561384
% 10.25/10.43  # Factorizations                       : 0
% 10.25/10.43  # Equation resolutions                 : 0
% 10.25/10.43  # Propositional unsat checks           : 0
% 10.25/10.43  #    Propositional check models        : 0
% 10.25/10.43  #    Propositional check unsatisfiable : 0
% 10.25/10.43  #    Propositional clauses             : 0
% 10.25/10.43  #    Propositional clauses after purity: 0
% 10.25/10.43  #    Propositional unsat core size     : 0
% 10.25/10.43  #    Propositional preprocessing time  : 0.000
% 10.25/10.43  #    Propositional encoding time       : 0.000
% 10.25/10.43  #    Propositional solver time         : 0.000
% 10.25/10.43  #    Success case prop preproc time    : 0.000
% 10.25/10.43  #    Success case prop encoding time   : 0.000
% 10.25/10.43  #    Success case prop solver time     : 0.000
% 10.25/10.43  # Current number of processed clauses  : 1934
% 10.25/10.43  #    Positive orientable unit clauses  : 1081
% 10.25/10.43  #    Positive unorientable unit clauses: 80
% 10.25/10.43  #    Negative unit clauses             : 1
% 10.25/10.43  #    Non-unit-clauses                  : 772
% 10.25/10.43  # Current number of unprocessed clauses: 529520
% 10.25/10.43  # ...number of literals in the above   : 676189
% 10.25/10.43  # Current number of archived formulas  : 0
% 10.25/10.43  # Current number of archived clauses   : 336
% 10.25/10.43  # Clause-clause subsumption calls (NU) : 25194
% 10.25/10.43  # Rec. Clause-clause subsumption calls : 25191
% 10.25/10.43  # Non-unit clause-clause subsumptions  : 1867
% 10.25/10.43  # Unit Clause-clause subsumption calls : 8300
% 10.25/10.43  # Rewrite failures with RHS unbound    : 0
% 10.25/10.43  # BW rewrite match attempts            : 13238
% 10.25/10.43  # BW rewrite match successes           : 324
% 10.25/10.43  # Condensation attempts                : 0
% 10.25/10.43  # Condensation successes               : 0
% 10.25/10.43  # Termbank termtop insertions          : 54044696
% 10.25/10.45  
% 10.25/10.45  # -------------------------------------------------
% 10.25/10.45  # User time                : 9.784 s
% 10.25/10.45  # System time              : 0.322 s
% 10.25/10.45  # Total time               : 10.106 s
% 10.25/10.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
