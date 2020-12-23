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
% DateTime   : Thu Dec  3 10:43:19 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  73 expanded)
%              Number of clauses        :   20 (  34 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  88 expanded)
%              Number of equality atoms :   12 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t97_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_8,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k3_xboole_0(X9,X10)) = X9 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_9,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X7,X8] : k3_xboole_0(X7,k2_xboole_0(X7,X8)) = X7 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_11,plain,(
    ! [X11,X12,X13] : r1_tarski(k2_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X13)),k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_18,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X4,X6)
      | r1_tarski(X4,k3_xboole_0(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k3_tarski(X18),k3_tarski(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_13]),c_0_13])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))) ),
    inference(assume_negation,[status(cth)],[t97_zfmisc_1])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

fof(c_0_26,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_27,negated_conjecture,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X3,k4_xboole_0(X3,k3_tarski(X2))))
    | ~ r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_tarski(k4_xboole_0(X1,X2)),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k3_tarski(esk1_0),k4_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_13]),c_0_13])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k3_tarski(X1),k4_xboole_0(k3_tarski(X1),k3_tarski(X2)))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:46:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.19/0.40  # and selection function SelectDiffNegLit.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.026 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.19/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.40  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.19/0.40  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.19/0.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.19/0.40  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.19/0.40  fof(t97_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 0.19/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.40  fof(c_0_8, plain, ![X9, X10]:k2_xboole_0(X9,k3_xboole_0(X9,X10))=X9, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.19/0.40  fof(c_0_9, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.40  fof(c_0_10, plain, ![X7, X8]:k3_xboole_0(X7,k2_xboole_0(X7,X8))=X7, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.19/0.40  fof(c_0_11, plain, ![X11, X12, X13]:r1_tarski(k2_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X13)),k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.19/0.40  cnf(c_0_12, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_14, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_15, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_16, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.40  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_14, c_0_13])).
% 0.19/0.40  fof(c_0_18, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X4,X6)|r1_tarski(X4,k3_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.19/0.40  fof(c_0_19, plain, ![X18, X19]:(~r1_tarski(X18,X19)|r1_tarski(k3_tarski(X18),k3_tarski(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.19/0.40  cnf(c_0_20, plain, (r1_tarski(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_13]), c_0_13])).
% 0.19/0.40  cnf(c_0_21, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.40  fof(c_0_22, negated_conjecture, ~(![X1, X2]:r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2)))), inference(assume_negation,[status(cth)],[t97_zfmisc_1])).
% 0.19/0.40  cnf(c_0_23, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_24, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.19/0.40  fof(c_0_26, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.40  fof(c_0_27, negated_conjecture, ~r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.40  cnf(c_0_28, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_13])).
% 0.19/0.40  cnf(c_0_29, plain, (r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k3_tarski(X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (~r1_tarski(k3_tarski(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_32, plain, (r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X3,k4_xboole_0(X3,k3_tarski(X2))))|~r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_33, plain, (r1_tarski(k3_tarski(k4_xboole_0(X1,X2)),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_24, c_0_30])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (~r1_tarski(k3_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k3_tarski(esk1_0),k4_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_13]), c_0_13])).
% 0.19/0.40  cnf(c_0_35, plain, (r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k3_tarski(X1),k4_xboole_0(k3_tarski(X1),k3_tarski(X2))))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 37
% 0.19/0.40  # Proof object clause steps            : 20
% 0.19/0.40  # Proof object formula steps           : 17
% 0.19/0.40  # Proof object conjectures             : 6
% 0.19/0.40  # Proof object clause conjectures      : 3
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 8
% 0.19/0.40  # Proof object initial formulas used   : 8
% 0.19/0.40  # Proof object generating inferences   : 6
% 0.19/0.40  # Proof object simplifying inferences  : 10
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 8
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 8
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 7
% 0.19/0.40  # Processed clauses                    : 180
% 0.19/0.40  # ...of these trivial                  : 14
% 0.19/0.40  # ...subsumed                          : 28
% 0.19/0.40  # ...remaining for further processing  : 138
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 1
% 0.19/0.40  # Generated clauses                    : 1983
% 0.19/0.40  # ...of the previous two non-trivial   : 1615
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 1983
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 130
% 0.19/0.40  #    Positive orientable unit clauses  : 100
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 0
% 0.19/0.40  #    Non-unit-clauses                  : 30
% 0.19/0.40  # Current number of unprocessed clauses: 1449
% 0.19/0.40  # ...number of literals in the above   : 1521
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 9
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 175
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 174
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 28
% 0.19/0.40  # Unit Clause-clause subsumption calls : 67
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 1265
% 0.19/0.40  # BW rewrite match successes           : 1
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 60440
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.063 s
% 0.19/0.40  # System time              : 0.002 s
% 0.19/0.40  # Total time               : 0.065 s
% 0.19/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
