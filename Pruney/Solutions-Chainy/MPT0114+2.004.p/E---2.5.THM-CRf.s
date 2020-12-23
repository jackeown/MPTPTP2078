%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:48 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 129 expanded)
%              Number of clauses        :   23 (  57 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 247 expanded)
%              Number of equality atoms :   19 (  73 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t107_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k5_xboole_0(X2,X3))
      <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t107_xboole_1])).

fof(c_0_9,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_10,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,negated_conjecture,
    ( ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
      | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) )
    & ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k2_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

fof(c_0_15,plain,(
    ! [X8,X9,X10] :
      ( ( r1_tarski(X8,X9)
        | ~ r1_tarski(X8,k4_xboole_0(X9,X10)) )
      & ( r1_xboole_0(X8,X10)
        | ~ r1_tarski(X8,k4_xboole_0(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,k2_xboole_0(X12,X13))
      | r1_tarski(k4_xboole_0(X11,X12),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_13]),c_0_17])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_13]),c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))
    | r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_13]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.55  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.38/0.55  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.38/0.55  #
% 0.38/0.55  # Preprocessing time       : 0.026 s
% 0.38/0.55  # Presaturation interreduction done
% 0.38/0.55  
% 0.38/0.55  # Proof found!
% 0.38/0.55  # SZS status Theorem
% 0.38/0.55  # SZS output start CNFRefutation
% 0.38/0.55  fof(t107_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.38/0.55  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.38/0.55  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.38/0.55  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.38/0.55  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.38/0.55  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.38/0.55  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.38/0.55  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.38/0.55  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t107_xboole_1])).
% 0.38/0.55  fof(c_0_9, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.38/0.55  fof(c_0_10, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.38/0.55  fof(c_0_11, negated_conjecture, ((~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|(~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))))&((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.38/0.55  cnf(c_0_12, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.38/0.55  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.38/0.55  fof(c_0_14, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k2_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.38/0.55  fof(c_0_15, plain, ![X8, X9, X10]:((r1_tarski(X8,X9)|~r1_tarski(X8,k4_xboole_0(X9,X10)))&(r1_xboole_0(X8,X10)|~r1_tarski(X8,k4_xboole_0(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.38/0.55  cnf(c_0_16, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.38/0.55  cnf(c_0_17, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.38/0.55  fof(c_0_18, plain, ![X11, X12, X13]:(~r1_tarski(X11,k2_xboole_0(X12,X13))|r1_tarski(k4_xboole_0(X11,X12),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.38/0.55  fof(c_0_19, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.38/0.55  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.38/0.55  fof(c_0_21, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.38/0.55  cnf(c_0_22, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.38/0.55  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.55  cnf(c_0_24, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.38/0.55  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.55  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.55  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_13]), c_0_17])).
% 0.38/0.55  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.55  cnf(c_0_29, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.38/0.55  cnf(c_0_30, negated_conjecture, (~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))|~r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_13]), c_0_17])).
% 0.38/0.55  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.38/0.55  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.38/0.55  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.38/0.55  cnf(c_0_34, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.38/0.55  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))|r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_13]), c_0_17])).
% 0.38/0.55  cnf(c_0_36, negated_conjecture, (~r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), c_0_32])).
% 0.38/0.55  cnf(c_0_37, plain, (r1_tarski(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.38/0.55  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))), inference(sr,[status(thm)],[c_0_35, c_0_36])).
% 0.38/0.55  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_31])]), ['proof']).
% 0.38/0.55  # SZS output end CNFRefutation
% 0.38/0.55  # Proof object total steps             : 40
% 0.38/0.55  # Proof object clause steps            : 23
% 0.38/0.55  # Proof object formula steps           : 17
% 0.38/0.55  # Proof object conjectures             : 13
% 0.38/0.55  # Proof object clause conjectures      : 10
% 0.38/0.55  # Proof object formula conjectures     : 3
% 0.38/0.55  # Proof object initial clauses used    : 11
% 0.38/0.55  # Proof object initial formulas used   : 8
% 0.38/0.55  # Proof object generating inferences   : 4
% 0.38/0.55  # Proof object simplifying inferences  : 16
% 0.38/0.55  # Training examples: 0 positive, 0 negative
% 0.38/0.55  # Parsed axioms                        : 8
% 0.38/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.55  # Initial clauses                      : 12
% 0.38/0.55  # Removed in clause preprocessing      : 2
% 0.38/0.55  # Initial clauses in saturation        : 10
% 0.38/0.55  # Processed clauses                    : 512
% 0.38/0.55  # ...of these trivial                  : 10
% 0.38/0.55  # ...subsumed                          : 323
% 0.38/0.55  # ...remaining for further processing  : 179
% 0.38/0.55  # Other redundant clauses eliminated   : 0
% 0.38/0.55  # Clauses deleted for lack of memory   : 0
% 0.38/0.55  # Backward-subsumed                    : 0
% 0.38/0.55  # Backward-rewritten                   : 2
% 0.38/0.55  # Generated clauses                    : 3475
% 0.38/0.55  # ...of the previous two non-trivial   : 3310
% 0.38/0.55  # Contextual simplify-reflections      : 1
% 0.38/0.55  # Paramodulations                      : 3474
% 0.38/0.55  # Factorizations                       : 0
% 0.38/0.55  # Equation resolutions                 : 0
% 0.38/0.55  # Propositional unsat checks           : 0
% 0.38/0.55  #    Propositional check models        : 0
% 0.38/0.55  #    Propositional check unsatisfiable : 0
% 0.38/0.55  #    Propositional clauses             : 0
% 0.38/0.55  #    Propositional clauses after purity: 0
% 0.38/0.55  #    Propositional unsat core size     : 0
% 0.38/0.55  #    Propositional preprocessing time  : 0.000
% 0.38/0.55  #    Propositional encoding time       : 0.000
% 0.38/0.55  #    Propositional solver time         : 0.000
% 0.38/0.55  #    Success case prop preproc time    : 0.000
% 0.38/0.55  #    Success case prop encoding time   : 0.000
% 0.38/0.55  #    Success case prop solver time     : 0.000
% 0.38/0.55  # Current number of processed clauses  : 166
% 0.38/0.55  #    Positive orientable unit clauses  : 12
% 0.38/0.55  #    Positive unorientable unit clauses: 1
% 0.38/0.55  #    Negative unit clauses             : 2
% 0.38/0.55  #    Non-unit-clauses                  : 151
% 0.38/0.55  # Current number of unprocessed clauses: 2814
% 0.38/0.55  # ...number of literals in the above   : 7466
% 0.38/0.55  # Current number of archived formulas  : 0
% 0.38/0.55  # Current number of archived clauses   : 15
% 0.38/0.55  # Clause-clause subsumption calls (NU) : 8221
% 0.38/0.55  # Rec. Clause-clause subsumption calls : 5811
% 0.38/0.55  # Non-unit clause-clause subsumptions  : 324
% 0.38/0.55  # Unit Clause-clause subsumption calls : 2
% 0.38/0.55  # Rewrite failures with RHS unbound    : 0
% 0.38/0.55  # BW rewrite match attempts            : 44
% 0.38/0.55  # BW rewrite match successes           : 1
% 0.38/0.55  # Condensation attempts                : 0
% 0.38/0.55  # Condensation successes               : 0
% 0.38/0.55  # Termbank termtop insertions          : 873194
% 0.38/0.55  
% 0.38/0.55  # -------------------------------------------------
% 0.38/0.55  # User time                : 0.201 s
% 0.38/0.55  # System time              : 0.005 s
% 0.38/0.55  # Total time               : 0.206 s
% 0.38/0.55  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
