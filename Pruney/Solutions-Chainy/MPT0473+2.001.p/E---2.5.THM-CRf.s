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
% DateTime   : Thu Dec  3 10:49:21 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 142 expanded)
%              Number of clauses        :   17 (  58 expanded)
%              Number of leaves         :    7 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 329 expanded)
%              Number of equality atoms :   21 ( 144 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(fc8_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc11_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k1_relat_1(X1) = k1_xboole_0
        <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t65_relat_1])).

fof(c_0_8,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | X2 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_9,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | v1_xboole_0(k1_relat_1(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

fof(c_0_10,plain,(
    ! [X6] :
      ( v1_xboole_0(X6)
      | ~ v1_relat_1(X6)
      | ~ v1_xboole_0(k2_relat_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ( k1_relat_1(esk1_0) != k1_xboole_0
      | k2_relat_1(esk1_0) != k1_xboole_0 )
    & ( k1_relat_1(esk1_0) = k1_xboole_0
      | k2_relat_1(esk1_0) = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X5] :
      ( v1_xboole_0(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_xboole_0(k1_relat_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(esk1_0) = k1_xboole_0
    | k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_19,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(esk1_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v1_xboole_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17]),c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

fof(c_0_24,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | v1_xboole_0(k2_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(esk1_0) != k1_xboole_0
    | k2_relat_1(esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_23]),c_0_26]),c_0_23])])).

cnf(c_0_29,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:18:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.18/0.37  # and selection function SelectNewComplexAHPNS.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.026 s
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t65_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.18/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.18/0.37  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.18/0.37  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.18/0.37  fof(fc8_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 0.18/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.37  fof(fc11_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 0.18/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t65_relat_1])).
% 0.18/0.37  fof(c_0_8, plain, ![X2]:(~v1_xboole_0(X2)|X2=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.18/0.37  fof(c_0_9, plain, ![X3]:(~v1_xboole_0(X3)|v1_xboole_0(k1_relat_1(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.18/0.37  fof(c_0_10, plain, ![X6]:(v1_xboole_0(X6)|~v1_relat_1(X6)|~v1_xboole_0(k2_relat_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.18/0.37  fof(c_0_11, negated_conjecture, (v1_relat_1(esk1_0)&((k1_relat_1(esk1_0)!=k1_xboole_0|k2_relat_1(esk1_0)!=k1_xboole_0)&(k1_relat_1(esk1_0)=k1_xboole_0|k2_relat_1(esk1_0)=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.18/0.37  cnf(c_0_12, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_13, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_14, plain, ![X5]:(v1_xboole_0(X5)|~v1_relat_1(X5)|~v1_xboole_0(k1_relat_1(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).
% 0.18/0.37  cnf(c_0_15, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (k1_relat_1(esk1_0)=k1_xboole_0|k2_relat_1(esk1_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_18, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.37  cnf(c_0_19, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.37  cnf(c_0_20, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_21, negated_conjecture, (k1_relat_1(esk1_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.37  cnf(c_0_22, negated_conjecture, (v1_xboole_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_17]), c_0_18])])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_22])).
% 0.18/0.37  fof(c_0_24, plain, ![X4]:(~v1_xboole_0(X4)|v1_xboole_0(k2_relat_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (k1_relat_1(esk1_0)!=k1_xboole_0|k2_relat_1(esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_26, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_23])).
% 0.18/0.37  cnf(c_0_27, plain, (v1_xboole_0(k2_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.37  cnf(c_0_28, negated_conjecture, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_23]), c_0_26]), c_0_23])])).
% 0.18/0.37  cnf(c_0_29, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_27])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_18])]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 31
% 0.18/0.37  # Proof object clause steps            : 17
% 0.18/0.37  # Proof object formula steps           : 14
% 0.18/0.37  # Proof object conjectures             : 12
% 0.18/0.37  # Proof object clause conjectures      : 9
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 9
% 0.18/0.37  # Proof object initial formulas used   : 7
% 0.18/0.37  # Proof object generating inferences   : 6
% 0.18/0.37  # Proof object simplifying inferences  : 14
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 7
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 9
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 9
% 0.18/0.37  # Processed clauses                    : 16
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 0
% 0.18/0.37  # ...remaining for further processing  : 16
% 0.18/0.37  # Other redundant clauses eliminated   : 0
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 4
% 0.18/0.37  # Generated clauses                    : 16
% 0.18/0.37  # ...of the previous two non-trivial   : 7
% 0.18/0.37  # Contextual simplify-reflections      : 1
% 0.18/0.37  # Paramodulations                      : 16
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 0
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 12
% 0.18/0.37  #    Positive orientable unit clauses  : 4
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 1
% 0.18/0.37  #    Non-unit-clauses                  : 7
% 0.18/0.37  # Current number of unprocessed clauses: 0
% 0.18/0.37  # ...number of literals in the above   : 0
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 4
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 4
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.18/0.37  # Unit Clause-clause subsumption calls : 0
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 2
% 0.18/0.37  # BW rewrite match successes           : 2
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 676
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.025 s
% 0.18/0.37  # System time              : 0.005 s
% 0.18/0.37  # Total time               : 0.030 s
% 0.18/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
