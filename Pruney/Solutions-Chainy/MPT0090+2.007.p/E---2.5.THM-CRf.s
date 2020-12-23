%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:43 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 453 expanded)
%              Number of clauses        :   35 ( 206 expanded)
%              Number of leaves         :    8 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :   77 ( 611 expanded)
%              Number of equality atoms :   48 ( 433 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t83_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_9,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X16,X17] : r1_xboole_0(k4_xboole_0(X16,X17),X17) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_11,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_17,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_15]),c_0_19])])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_13]),c_0_13])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24]),c_0_23]),c_0_15]),c_0_15])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_13])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_15])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = X1
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(X1,X2)
      <=> k4_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t83_xboole_1])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_25])).

fof(c_0_42,negated_conjecture,
    ( ( ~ r1_xboole_0(esk1_0,esk2_0)
      | k4_xboole_0(esk1_0,esk2_0) != esk1_0 )
    & ( r1_xboole_0(esk1_0,esk2_0)
      | k4_xboole_0(esk1_0,esk2_0) = esk1_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_18]),c_0_15]),c_0_20]),c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    | k4_xboole_0(esk1_0,esk2_0) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n009.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 16:24:56 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.31  # No SInE strategy applied
% 0.10/0.31  # Trying AutoSched0 for 299 seconds
% 0.15/0.47  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.15/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.47  #
% 0.15/0.47  # Preprocessing time       : 0.026 s
% 0.15/0.47  # Presaturation interreduction done
% 0.15/0.47  
% 0.15/0.47  # Proof found!
% 0.15/0.47  # SZS status Theorem
% 0.15/0.47  # SZS output start CNFRefutation
% 0.15/0.47  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.15/0.47  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.15/0.47  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.15/0.47  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.15/0.47  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.15/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.15/0.47  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.15/0.47  fof(t83_xboole_1, conjecture, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.15/0.47  fof(c_0_8, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.15/0.47  fof(c_0_9, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.15/0.47  fof(c_0_10, plain, ![X16, X17]:r1_xboole_0(k4_xboole_0(X16,X17),X17), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.15/0.47  fof(c_0_11, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.15/0.47  cnf(c_0_12, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.47  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.47  cnf(c_0_14, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.47  cnf(c_0_15, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.47  fof(c_0_16, plain, ![X11, X12, X13]:k4_xboole_0(k4_xboole_0(X11,X12),X13)=k4_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.15/0.47  fof(c_0_17, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.15/0.47  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.15/0.47  cnf(c_0_19, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.15/0.47  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.47  fof(c_0_21, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.15/0.47  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.47  cnf(c_0_23, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_15]), c_0_19])])).
% 0.15/0.47  cnf(c_0_24, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 0.15/0.47  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.47  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_13]), c_0_13])).
% 0.15/0.47  cnf(c_0_27, plain, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.47  cnf(c_0_28, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)=k2_xboole_0(k4_xboole_0(X1,X2),X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.15/0.47  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_24]), c_0_23]), c_0_15]), c_0_15])).
% 0.15/0.47  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.47  cnf(c_0_31, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.15/0.47  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_13])).
% 0.15/0.47  cnf(c_0_33, plain, (k2_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.15/0.47  cnf(c_0_34, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_23]), c_0_15])).
% 0.15/0.47  cnf(c_0_35, plain, (k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.15/0.47  cnf(c_0_36, plain, (k2_xboole_0(k1_xboole_0,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.15/0.47  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=X1|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_15])).
% 0.15/0.47  fof(c_0_38, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1)), inference(assume_negation,[status(cth)],[t83_xboole_1])).
% 0.15/0.47  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.15/0.47  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 0.15/0.47  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_25])).
% 0.15/0.47  fof(c_0_42, negated_conjecture, ((~r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)!=esk1_0)&(r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 0.15/0.47  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_18])).
% 0.15/0.47  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_18]), c_0_15]), c_0_20]), c_0_41])])).
% 0.15/0.47  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)=esk1_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.15/0.47  cnf(c_0_46, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_43, c_0_14])).
% 0.15/0.47  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.15/0.47  cnf(c_0_48, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.15/0.47  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.15/0.47  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_47])])).
% 0.15/0.47  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_49]), c_0_50]), ['proof']).
% 0.15/0.47  # SZS output end CNFRefutation
% 0.15/0.47  # Proof object total steps             : 52
% 0.15/0.47  # Proof object clause steps            : 35
% 0.15/0.47  # Proof object formula steps           : 17
% 0.15/0.47  # Proof object conjectures             : 9
% 0.15/0.47  # Proof object clause conjectures      : 6
% 0.15/0.47  # Proof object formula conjectures     : 3
% 0.15/0.47  # Proof object initial clauses used    : 10
% 0.15/0.47  # Proof object initial formulas used   : 8
% 0.15/0.47  # Proof object generating inferences   : 20
% 0.15/0.47  # Proof object simplifying inferences  : 21
% 0.15/0.47  # Training examples: 0 positive, 0 negative
% 0.15/0.47  # Parsed axioms                        : 8
% 0.15/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.47  # Initial clauses                      : 10
% 0.15/0.47  # Removed in clause preprocessing      : 1
% 0.15/0.47  # Initial clauses in saturation        : 9
% 0.15/0.47  # Processed clauses                    : 1721
% 0.15/0.47  # ...of these trivial                  : 29
% 0.15/0.47  # ...subsumed                          : 1421
% 0.15/0.47  # ...remaining for further processing  : 271
% 0.15/0.47  # Other redundant clauses eliminated   : 0
% 0.15/0.47  # Clauses deleted for lack of memory   : 0
% 0.15/0.47  # Backward-subsumed                    : 20
% 0.15/0.47  # Backward-rewritten                   : 28
% 0.15/0.47  # Generated clauses                    : 12721
% 0.15/0.47  # ...of the previous two non-trivial   : 10008
% 0.15/0.47  # Contextual simplify-reflections      : 0
% 0.15/0.47  # Paramodulations                      : 12720
% 0.15/0.47  # Factorizations                       : 0
% 0.15/0.47  # Equation resolutions                 : 1
% 0.15/0.47  # Propositional unsat checks           : 0
% 0.15/0.47  #    Propositional check models        : 0
% 0.15/0.47  #    Propositional check unsatisfiable : 0
% 0.15/0.47  #    Propositional clauses             : 0
% 0.15/0.47  #    Propositional clauses after purity: 0
% 0.15/0.47  #    Propositional unsat core size     : 0
% 0.15/0.47  #    Propositional preprocessing time  : 0.000
% 0.15/0.47  #    Propositional encoding time       : 0.000
% 0.15/0.47  #    Propositional solver time         : 0.000
% 0.15/0.47  #    Success case prop preproc time    : 0.000
% 0.15/0.47  #    Success case prop encoding time   : 0.000
% 0.15/0.47  #    Success case prop solver time     : 0.000
% 0.15/0.47  # Current number of processed clauses  : 214
% 0.15/0.47  #    Positive orientable unit clauses  : 49
% 0.15/0.47  #    Positive unorientable unit clauses: 4
% 0.15/0.47  #    Negative unit clauses             : 4
% 0.15/0.47  #    Non-unit-clauses                  : 157
% 0.15/0.47  # Current number of unprocessed clauses: 8123
% 0.15/0.47  # ...number of literals in the above   : 18606
% 0.15/0.47  # Current number of archived formulas  : 0
% 0.15/0.47  # Current number of archived clauses   : 58
% 0.15/0.47  # Clause-clause subsumption calls (NU) : 14025
% 0.15/0.47  # Rec. Clause-clause subsumption calls : 11757
% 0.15/0.47  # Non-unit clause-clause subsumptions  : 1426
% 0.15/0.47  # Unit Clause-clause subsumption calls : 89
% 0.15/0.47  # Rewrite failures with RHS unbound    : 0
% 0.15/0.47  # BW rewrite match attempts            : 233
% 0.15/0.47  # BW rewrite match successes           : 24
% 0.15/0.47  # Condensation attempts                : 0
% 0.15/0.47  # Condensation successes               : 0
% 0.15/0.47  # Termbank termtop insertions          : 131364
% 0.15/0.47  
% 0.15/0.47  # -------------------------------------------------
% 0.15/0.47  # User time                : 0.154 s
% 0.15/0.47  # System time              : 0.013 s
% 0.15/0.47  # Total time               : 0.167 s
% 0.15/0.47  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
