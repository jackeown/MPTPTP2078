%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:17 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 101 expanded)
%              Number of clauses        :   31 (  45 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 151 expanded)
%              Number of equality atoms :   41 (  81 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_xboole_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    inference(assume_negation,[status(cth)],[t75_xboole_1])).

fof(c_0_13,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    & r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k3_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ( k4_xboole_0(X25,X26) != k1_xboole_0
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | k4_xboole_0(X25,X26) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_23,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X29,X30] : k2_xboole_0(X29,k4_xboole_0(X30,X29)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_30,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,k4_xboole_0(X28,X27))
      | X27 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_18]),c_0_18])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

fof(c_0_47,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k2_xboole_0(X33,X34)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_46])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_49]),c_0_41])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:33:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.19/0.37  # and selection function SelectNewComplexAHP.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t75_xboole_1, conjecture, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.19/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.37  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.37  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.19/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.38  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.19/0.38  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2)))), inference(assume_negation,[status(cth)],[t75_xboole_1])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)&r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X35, X36]:k4_xboole_0(X35,k4_xboole_0(X35,X36))=k3_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.38  fof(c_0_15, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.38  fof(c_0_16, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  fof(c_0_22, plain, ![X25, X26]:((k4_xboole_0(X25,X26)!=k1_xboole_0|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|k4_xboole_0(X25,X26)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.19/0.38  fof(c_0_23, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  fof(c_0_26, plain, ![X29, X30]:k2_xboole_0(X29,k4_xboole_0(X30,X29))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.38  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  fof(c_0_29, plain, ![X21]:k2_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.38  fof(c_0_30, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.38  fof(c_0_31, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_34, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_36, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  fof(c_0_38, plain, ![X27, X28]:(~r1_tarski(X27,k4_xboole_0(X28,X27))|X27=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.19/0.38  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_41, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.38  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_18]), c_0_18])).
% 0.19/0.38  cnf(c_0_43, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.19/0.38  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.19/0.38  fof(c_0_47, plain, ![X33, X34]:k4_xboole_0(X33,k2_xboole_0(X33,X34))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.38  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_46])).
% 0.19/0.38  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_18])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_49]), c_0_41])).
% 0.19/0.38  cnf(c_0_53, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), c_0_54]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 56
% 0.19/0.38  # Proof object clause steps            : 31
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 14
% 0.19/0.38  # Proof object clause conjectures      : 11
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 15
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 12
% 0.19/0.38  # Proof object simplifying inferences  : 13
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 20
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 26
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 25
% 0.19/0.38  # Processed clauses                    : 130
% 0.19/0.38  # ...of these trivial                  : 32
% 0.19/0.38  # ...subsumed                          : 7
% 0.19/0.38  # ...remaining for further processing  : 91
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 8
% 0.19/0.38  # Generated clauses                    : 721
% 0.19/0.38  # ...of the previous two non-trivial   : 219
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 718
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 3
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 58
% 0.19/0.38  #    Positive orientable unit clauses  : 38
% 0.19/0.38  #    Positive unorientable unit clauses: 2
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 17
% 0.19/0.38  # Current number of unprocessed clauses: 133
% 0.19/0.38  # ...number of literals in the above   : 157
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 34
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 20
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 20
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.19/0.38  # Unit Clause-clause subsumption calls : 2
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 47
% 0.19/0.38  # BW rewrite match successes           : 22
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5565
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
