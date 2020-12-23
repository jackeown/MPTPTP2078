%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:55 EST 2020

% Result     : Theorem 43.42s
% Output     : CNFRefutation 43.42s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 938 expanded)
%              Number of clauses        :   36 ( 419 expanded)
%              Number of leaves         :    8 ( 257 expanded)
%              Depth                    :   16
%              Number of atoms          :   99 (1152 expanded)
%              Number of equality atoms :   38 ( 907 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_8,plain,(
    ! [X16,X17] : k2_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = X16 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_9,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_10,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_13,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_14,plain,(
    ! [X8] : k3_xboole_0(X8,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_21])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23]),c_0_23])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_17])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_17]),c_0_32])])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_11])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_35]),c_0_16]),c_0_19]),c_0_21])).

fof(c_0_39,negated_conjecture,
    ( ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk3_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0)
    | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k4_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_29])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 43.42/43.66  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 43.42/43.66  # and selection function SelectMaxLComplexAvoidPosPred.
% 43.42/43.66  #
% 43.42/43.66  # Preprocessing time       : 0.027 s
% 43.42/43.66  # Presaturation interreduction done
% 43.42/43.66  
% 43.42/43.66  # Proof found!
% 43.42/43.66  # SZS status Theorem
% 43.42/43.66  # SZS output start CNFRefutation
% 43.42/43.66  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 43.42/43.66  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 43.42/43.66  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 43.42/43.66  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 43.42/43.66  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 43.42/43.66  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 43.42/43.66  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 43.42/43.66  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 43.42/43.66  fof(c_0_8, plain, ![X16, X17]:k2_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,X17))=X16, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 43.42/43.66  fof(c_0_9, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 43.42/43.66  cnf(c_0_10, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 43.42/43.66  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 43.42/43.66  fof(c_0_12, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 43.42/43.66  fof(c_0_13, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 43.42/43.66  fof(c_0_14, plain, ![X8]:k3_xboole_0(X8,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 43.42/43.66  cnf(c_0_15, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 43.42/43.66  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 43.42/43.66  cnf(c_0_17, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 43.42/43.66  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 43.42/43.66  cnf(c_0_19, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_16])).
% 43.42/43.66  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 43.42/43.66  cnf(c_0_21, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 43.42/43.66  fof(c_0_22, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 43.42/43.66  cnf(c_0_23, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_16, c_0_21])).
% 43.42/43.66  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 43.42/43.66  fof(c_0_25, plain, ![X11, X12, X13]:k4_xboole_0(k4_xboole_0(X11,X12),X13)=k4_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 43.42/43.66  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_23]), c_0_23])).
% 43.42/43.66  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_11])).
% 43.42/43.66  cnf(c_0_28, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 43.42/43.66  cnf(c_0_29, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_26])).
% 43.42/43.66  cnf(c_0_30, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 43.42/43.66  cnf(c_0_31, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 43.42/43.66  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_17])).
% 43.42/43.66  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 43.42/43.66  cnf(c_0_34, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_17]), c_0_32])])).
% 43.42/43.66  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_11])).
% 43.42/43.66  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 43.42/43.66  cnf(c_0_37, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 43.42/43.66  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_35]), c_0_16]), c_0_19]), c_0_21])).
% 43.42/43.66  fof(c_0_39, negated_conjecture, ((((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk2_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk3_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])])).
% 43.42/43.66  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 43.42/43.66  cnf(c_0_41, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 43.42/43.66  cnf(c_0_42, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 43.42/43.66  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 43.42/43.66  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_40, c_0_16])).
% 43.42/43.66  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 43.42/43.66  cnf(c_0_46, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k4_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 43.42/43.66  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 43.42/43.66  cnf(c_0_48, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 43.42/43.66  cnf(c_0_49, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_46])).
% 43.42/43.66  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 43.42/43.66  cnf(c_0_51, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_29])])).
% 43.42/43.66  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_43]), c_0_48])]), ['proof']).
% 43.42/43.66  # SZS output end CNFRefutation
% 43.42/43.66  # Proof object total steps             : 53
% 43.42/43.66  # Proof object clause steps            : 36
% 43.42/43.66  # Proof object formula steps           : 17
% 43.42/43.66  # Proof object conjectures             : 11
% 43.42/43.66  # Proof object clause conjectures      : 8
% 43.42/43.66  # Proof object formula conjectures     : 3
% 43.42/43.66  # Proof object initial clauses used    : 11
% 43.42/43.66  # Proof object initial formulas used   : 8
% 43.42/43.66  # Proof object generating inferences   : 17
% 43.42/43.66  # Proof object simplifying inferences  : 26
% 43.42/43.66  # Training examples: 0 positive, 0 negative
% 43.42/43.66  # Parsed axioms                        : 8
% 43.42/43.66  # Removed by relevancy pruning/SinE    : 0
% 43.42/43.66  # Initial clauses                      : 14
% 43.42/43.66  # Removed in clause preprocessing      : 4
% 43.42/43.66  # Initial clauses in saturation        : 10
% 43.42/43.66  # Processed clauses                    : 72628
% 43.42/43.66  # ...of these trivial                  : 863
% 43.42/43.66  # ...subsumed                          : 67760
% 43.42/43.66  # ...remaining for further processing  : 4005
% 43.42/43.66  # Other redundant clauses eliminated   : 0
% 43.42/43.66  # Clauses deleted for lack of memory   : 792276
% 43.42/43.66  # Backward-subsumed                    : 269
% 43.42/43.66  # Backward-rewritten                   : 735
% 43.42/43.66  # Generated clauses                    : 3915035
% 43.42/43.66  # ...of the previous two non-trivial   : 3621441
% 43.42/43.66  # Contextual simplify-reflections      : 145
% 43.42/43.66  # Paramodulations                      : 3915031
% 43.42/43.66  # Factorizations                       : 0
% 43.42/43.66  # Equation resolutions                 : 4
% 43.42/43.66  # Propositional unsat checks           : 0
% 43.42/43.66  #    Propositional check models        : 0
% 43.42/43.66  #    Propositional check unsatisfiable : 0
% 43.42/43.66  #    Propositional clauses             : 0
% 43.42/43.66  #    Propositional clauses after purity: 0
% 43.42/43.66  #    Propositional unsat core size     : 0
% 43.42/43.66  #    Propositional preprocessing time  : 0.000
% 43.42/43.66  #    Propositional encoding time       : 0.000
% 43.42/43.66  #    Propositional solver time         : 0.000
% 43.42/43.66  #    Success case prop preproc time    : 0.000
% 43.42/43.66  #    Success case prop encoding time   : 0.000
% 43.42/43.66  #    Success case prop solver time     : 0.000
% 43.42/43.66  # Current number of processed clauses  : 2991
% 43.42/43.66  #    Positive orientable unit clauses  : 283
% 43.42/43.66  #    Positive unorientable unit clauses: 6
% 43.42/43.66  #    Negative unit clauses             : 94
% 43.42/43.66  #    Non-unit-clauses                  : 2608
% 43.42/43.66  # Current number of unprocessed clauses: 1323325
% 43.42/43.66  # ...number of literals in the above   : 3991782
% 43.42/43.66  # Current number of archived formulas  : 0
% 43.42/43.66  # Current number of archived clauses   : 1015
% 43.42/43.66  # Clause-clause subsumption calls (NU) : 1074326
% 43.42/43.66  # Rec. Clause-clause subsumption calls : 911204
% 43.42/43.66  # Non-unit clause-clause subsumptions  : 29258
% 43.42/43.66  # Unit Clause-clause subsumption calls : 16901
% 43.42/43.66  # Rewrite failures with RHS unbound    : 0
% 43.42/43.66  # BW rewrite match attempts            : 18813
% 43.42/43.66  # BW rewrite match successes           : 1383
% 43.42/43.66  # Condensation attempts                : 0
% 43.42/43.66  # Condensation successes               : 0
% 43.42/43.66  # Termbank termtop insertions          : 67793408
% 43.51/43.74  
% 43.51/43.74  # -------------------------------------------------
% 43.51/43.74  # User time                : 42.218 s
% 43.51/43.74  # System time              : 1.152 s
% 43.51/43.74  # Total time               : 43.369 s
% 43.51/43.74  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
