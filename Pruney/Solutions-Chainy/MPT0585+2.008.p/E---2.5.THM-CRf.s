%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 (  64 expanded)
%              Number of clauses        :   17 (  28 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 127 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t189_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X8)
      | k7_relat_1(k7_relat_1(X8,X6),X7) = k7_relat_1(X8,k3_xboole_0(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_6,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_7,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | k1_relat_1(k7_relat_1(X10,X9)) = k3_xboole_0(k1_relat_1(X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_10,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_11,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k7_relat_1(X11,k1_relat_1(X11)) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t189_relat_1])).

cnf(c_0_13,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_10])).

cnf(c_0_15,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k7_relat_1(esk1_0,k1_relat_1(esk2_0)) != k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k1_relat_1(X2)) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_13])).

cnf(c_0_18,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k1_relat_1(X1)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k7_relat_1(esk1_0,k1_relat_1(esk2_0)) != k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k7_relat_1(k7_relat_1(X1,k1_relat_1(X1)),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_24,plain,
    ( k7_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk2_0)))) != k7_relat_1(esk1_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.049 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.13/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.40  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.13/0.40  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.13/0.40  fof(t189_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 0.13/0.40  fof(c_0_5, plain, ![X6, X7, X8]:(~v1_relat_1(X8)|k7_relat_1(k7_relat_1(X8,X6),X7)=k7_relat_1(X8,k3_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.13/0.40  fof(c_0_6, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.40  cnf(c_0_7, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_8, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  fof(c_0_9, plain, ![X9, X10]:(~v1_relat_1(X10)|k1_relat_1(k7_relat_1(X10,X9))=k3_xboole_0(k1_relat_1(X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.13/0.40  cnf(c_0_10, plain, (k7_relat_1(X1,k3_xboole_0(X2,X3))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.40  fof(c_0_11, plain, ![X11]:(~v1_relat_1(X11)|k7_relat_1(X11,k1_relat_1(X11))=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.13/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t189_relat_1])).
% 0.13/0.40  cnf(c_0_13, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_14, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_7, c_0_10])).
% 0.13/0.40  cnf(c_0_15, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  fof(c_0_16, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&k7_relat_1(esk1_0,k1_relat_1(esk2_0))!=k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.40  cnf(c_0_17, plain, (k3_xboole_0(X1,k1_relat_1(X2))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_8, c_0_13])).
% 0.13/0.40  cnf(c_0_18, plain, (k7_relat_1(k7_relat_1(X1,X2),k1_relat_1(X1))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.40  cnf(c_0_19, negated_conjecture, (k7_relat_1(esk1_0,k1_relat_1(esk2_0))!=k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_20, plain, (k1_relat_1(k7_relat_1(X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_17])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_23, plain, (k7_relat_1(k7_relat_1(X1,k1_relat_1(X1)),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.13/0.40  cnf(c_0_24, plain, (k7_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3)=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_7, c_0_13])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk2_0))))!=k7_relat_1(esk1_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_26, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_22])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 28
% 0.13/0.40  # Proof object clause steps            : 17
% 0.13/0.40  # Proof object formula steps           : 11
% 0.13/0.40  # Proof object conjectures             : 8
% 0.13/0.40  # Proof object clause conjectures      : 5
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 7
% 0.13/0.40  # Proof object initial formulas used   : 5
% 0.13/0.40  # Proof object generating inferences   : 10
% 0.13/0.40  # Proof object simplifying inferences  : 5
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 5
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 7
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 7
% 0.13/0.40  # Processed clauses                    : 43
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 18
% 0.13/0.40  # ...remaining for further processing  : 25
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 0
% 0.13/0.40  # Generated clauses                    : 153
% 0.13/0.40  # ...of the previous two non-trivial   : 135
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 153
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 18
% 0.13/0.40  #    Positive orientable unit clauses  : 2
% 0.13/0.40  #    Positive unorientable unit clauses: 1
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 13
% 0.13/0.40  # Current number of unprocessed clauses: 106
% 0.13/0.40  # ...number of literals in the above   : 388
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 7
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 79
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 79
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 17
% 0.13/0.40  # Unit Clause-clause subsumption calls : 1
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 2
% 0.13/0.40  # BW rewrite match successes           : 2
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 2597
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.054 s
% 0.13/0.40  # System time              : 0.004 s
% 0.13/0.40  # Total time               : 0.058 s
% 0.13/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
