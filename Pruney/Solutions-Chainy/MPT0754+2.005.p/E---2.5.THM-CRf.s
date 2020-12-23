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
% DateTime   : Thu Dec  3 10:56:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   15 (  34 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   53 ( 216 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_ordinal1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v5_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v5_ordinal1(X3) )
         => ( v1_relat_1(X3)
            & v5_relat_1(X3,X2)
            & v1_funct_1(X3)
            & v5_ordinal1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).

fof(t218_relat_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v5_relat_1(X3,X1) )
         => v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v5_relat_1(X3,X1)
              & v1_funct_1(X3)
              & v5_ordinal1(X3) )
           => ( v1_relat_1(X3)
              & v5_relat_1(X3,X2)
              & v1_funct_1(X3)
              & v5_ordinal1(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_ordinal1])).

fof(c_0_3,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ v1_relat_1(X6)
      | ~ v5_relat_1(X6,X4)
      | v5_relat_1(X6,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t218_relat_1])])])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & v1_relat_1(esk3_0)
    & v5_relat_1(esk3_0,esk1_0)
    & v1_funct_1(esk3_0)
    & v5_ordinal1(esk3_0)
    & ( ~ v1_relat_1(esk3_0)
      | ~ v5_relat_1(esk3_0,esk2_0)
      | ~ v1_funct_1(esk3_0)
      | ~ v5_ordinal1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( v5_relat_1(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v5_relat_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ v5_relat_1(esk3_0,esk2_0)
    | ~ v1_funct_1(esk3_0)
    | ~ v5_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( v5_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( v5_relat_1(X1,esk2_0)
    | ~ v5_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( ~ v5_relat_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_12])]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:51:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.36  # and selection function SelectNegativeLiterals.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t47_ordinal1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((((v1_relat_1(X3)&v5_relat_1(X3,X1))&v1_funct_1(X3))&v5_ordinal1(X3))=>(((v1_relat_1(X3)&v5_relat_1(X3,X2))&v1_funct_1(X3))&v5_ordinal1(X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_ordinal1)).
% 0.13/0.36  fof(t218_relat_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v5_relat_1(X3,X1))=>v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 0.13/0.36  fof(c_0_2, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((((v1_relat_1(X3)&v5_relat_1(X3,X1))&v1_funct_1(X3))&v5_ordinal1(X3))=>(((v1_relat_1(X3)&v5_relat_1(X3,X2))&v1_funct_1(X3))&v5_ordinal1(X3))))), inference(assume_negation,[status(cth)],[t47_ordinal1])).
% 0.13/0.36  fof(c_0_3, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|(~v1_relat_1(X6)|~v5_relat_1(X6,X4)|v5_relat_1(X6,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t218_relat_1])])])).
% 0.13/0.36  fof(c_0_4, negated_conjecture, (r1_tarski(esk1_0,esk2_0)&((((v1_relat_1(esk3_0)&v5_relat_1(esk3_0,esk1_0))&v1_funct_1(esk3_0))&v5_ordinal1(esk3_0))&(~v1_relat_1(esk3_0)|~v5_relat_1(esk3_0,esk2_0)|~v1_funct_1(esk3_0)|~v5_ordinal1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).
% 0.13/0.36  cnf(c_0_5, plain, (v5_relat_1(X3,X2)|~r1_tarski(X1,X2)|~v1_relat_1(X3)|~v5_relat_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.36  cnf(c_0_6, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_7, negated_conjecture, (~v1_relat_1(esk3_0)|~v5_relat_1(esk3_0,esk2_0)|~v1_funct_1(esk3_0)|~v5_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_8, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_10, negated_conjecture, (v5_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_11, negated_conjecture, (v5_relat_1(X1,esk2_0)|~v5_relat_1(X1,esk1_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_5, c_0_6])).
% 0.13/0.36  cnf(c_0_12, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_13, negated_conjecture, (~v5_relat_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10])])).
% 0.13/0.36  cnf(c_0_14, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_8]), c_0_12])]), c_0_13]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 15
% 0.13/0.36  # Proof object clause steps            : 10
% 0.13/0.36  # Proof object formula steps           : 5
% 0.13/0.36  # Proof object conjectures             : 12
% 0.13/0.36  # Proof object clause conjectures      : 9
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 7
% 0.13/0.36  # Proof object initial formulas used   : 2
% 0.13/0.36  # Proof object generating inferences   : 2
% 0.13/0.36  # Proof object simplifying inferences  : 7
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 2
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 7
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 7
% 0.13/0.36  # Processed clauses                    : 15
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 15
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 2
% 0.13/0.36  # ...of the previous two non-trivial   : 1
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 2
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 8
% 0.13/0.36  #    Positive orientable unit clauses  : 5
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 2
% 0.13/0.36  # Current number of unprocessed clauses: 0
% 0.13/0.36  # ...number of literals in the above   : 0
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 7
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 468
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.025 s
% 0.13/0.36  # System time              : 0.004 s
% 0.13/0.36  # Total time               : 0.029 s
% 0.13/0.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
