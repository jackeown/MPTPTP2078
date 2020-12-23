%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:03 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   16 (  22 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   65 (  83 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X4) )
     => m1_subset_1(k1_tarski(k4_tarski(X1,X3)),k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r2_hidden(X1,X2)
          & r2_hidden(X3,X4) )
       => m1_subset_1(k1_tarski(k4_tarski(X1,X3)),k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ),
    inference(assume_negation,[status(cth)],[t8_relset_1])).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X10,X13,X14,X15,X16,X17,X18,X20,X21] :
      ( ( r2_hidden(esk1_4(X7,X8,X9,X10),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( r2_hidden(esk2_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( X10 = k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(X14,X7)
        | ~ r2_hidden(X15,X8)
        | X13 != k4_tarski(X14,X15)
        | r2_hidden(X13,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(X20,X16)
        | ~ r2_hidden(X21,X17)
        | esk3_3(X16,X17,X18) != k4_tarski(X20,X21)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk4_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk5_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( esk3_3(X16,X17,X18) = k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    & r2_hidden(esk8_0,esk9_0)
    & ~ m1_subset_1(k1_tarski(k4_tarski(esk6_0,esk8_0)),k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk9_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | m1_subset_1(k1_tarski(X24),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_7,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(esk6_0,esk8_0)),k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk8_0),k2_zfmisc_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:38:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.34  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.12/0.34  # and selection function SelectVGNonCR.
% 0.12/0.34  #
% 0.12/0.34  # Preprocessing time       : 0.012 s
% 0.12/0.34  # Presaturation interreduction done
% 0.12/0.34  
% 0.12/0.34  # Proof found!
% 0.12/0.34  # SZS status Theorem
% 0.12/0.34  # SZS output start CNFRefutation
% 0.12/0.34  fof(t8_relset_1, conjecture, ![X1, X2, X3, X4]:((r2_hidden(X1,X2)&r2_hidden(X3,X4))=>m1_subset_1(k1_tarski(k4_tarski(X1,X3)),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_relset_1)).
% 0.12/0.34  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.12/0.34  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.12/0.34  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:((r2_hidden(X1,X2)&r2_hidden(X3,X4))=>m1_subset_1(k1_tarski(k4_tarski(X1,X3)),k1_zfmisc_1(k2_zfmisc_1(X2,X4))))), inference(assume_negation,[status(cth)],[t8_relset_1])).
% 0.12/0.34  fof(c_0_4, plain, ![X7, X8, X9, X10, X13, X14, X15, X16, X17, X18, X20, X21]:(((((r2_hidden(esk1_4(X7,X8,X9,X10),X7)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8))&(r2_hidden(esk2_4(X7,X8,X9,X10),X8)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(X10=k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(~r2_hidden(X14,X7)|~r2_hidden(X15,X8)|X13!=k4_tarski(X14,X15)|r2_hidden(X13,X9)|X9!=k2_zfmisc_1(X7,X8)))&((~r2_hidden(esk3_3(X16,X17,X18),X18)|(~r2_hidden(X20,X16)|~r2_hidden(X21,X17)|esk3_3(X16,X17,X18)!=k4_tarski(X20,X21))|X18=k2_zfmisc_1(X16,X17))&(((r2_hidden(esk4_3(X16,X17,X18),X16)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))&(r2_hidden(esk5_3(X16,X17,X18),X17)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17)))&(esk3_3(X16,X17,X18)=k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.12/0.34  fof(c_0_5, negated_conjecture, ((r2_hidden(esk6_0,esk7_0)&r2_hidden(esk8_0,esk9_0))&~m1_subset_1(k1_tarski(k4_tarski(esk6_0,esk8_0)),k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.34  fof(c_0_6, plain, ![X24, X25]:(~r2_hidden(X24,X25)|m1_subset_1(k1_tarski(X24),k1_zfmisc_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.12/0.34  cnf(c_0_7, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.34  cnf(c_0_8, negated_conjecture, (~m1_subset_1(k1_tarski(k4_tarski(esk6_0,esk8_0)),k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.34  cnf(c_0_9, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.34  cnf(c_0_10, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|X1!=k4_tarski(X4,X5)|~r2_hidden(X5,X3)|~r2_hidden(X4,X2)), inference(er,[status(thm)],[c_0_7])).
% 0.12/0.34  cnf(c_0_11, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,esk8_0),k2_zfmisc_1(esk7_0,esk9_0))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.34  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_10])).
% 0.12/0.34  cnf(c_0_13, negated_conjecture, (r2_hidden(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.34  cnf(c_0_14, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.34  cnf(c_0_15, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])]), ['proof']).
% 0.12/0.34  # SZS output end CNFRefutation
% 0.12/0.34  # Proof object total steps             : 16
% 0.12/0.34  # Proof object clause steps            : 9
% 0.12/0.34  # Proof object formula steps           : 7
% 0.12/0.34  # Proof object conjectures             : 8
% 0.12/0.34  # Proof object clause conjectures      : 5
% 0.12/0.34  # Proof object formula conjectures     : 3
% 0.12/0.34  # Proof object initial clauses used    : 5
% 0.12/0.34  # Proof object initial formulas used   : 3
% 0.12/0.34  # Proof object generating inferences   : 4
% 0.12/0.34  # Proof object simplifying inferences  : 3
% 0.12/0.34  # Training examples: 0 positive, 0 negative
% 0.12/0.34  # Parsed axioms                        : 3
% 0.12/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.34  # Initial clauses                      : 12
% 0.12/0.34  # Removed in clause preprocessing      : 0
% 0.12/0.34  # Initial clauses in saturation        : 12
% 0.12/0.34  # Processed clauses                    : 28
% 0.12/0.34  # ...of these trivial                  : 0
% 0.12/0.34  # ...subsumed                          : 0
% 0.12/0.34  # ...remaining for further processing  : 28
% 0.12/0.34  # Other redundant clauses eliminated   : 0
% 0.12/0.34  # Clauses deleted for lack of memory   : 0
% 0.12/0.34  # Backward-subsumed                    : 0
% 0.12/0.34  # Backward-rewritten                   : 0
% 0.12/0.34  # Generated clauses                    : 12
% 0.12/0.34  # ...of the previous two non-trivial   : 11
% 0.12/0.34  # Contextual simplify-reflections      : 0
% 0.12/0.34  # Paramodulations                      : 9
% 0.12/0.34  # Factorizations                       : 0
% 0.12/0.34  # Equation resolutions                 : 3
% 0.12/0.34  # Propositional unsat checks           : 0
% 0.12/0.34  #    Propositional check models        : 0
% 0.12/0.34  #    Propositional check unsatisfiable : 0
% 0.12/0.34  #    Propositional clauses             : 0
% 0.12/0.34  #    Propositional clauses after purity: 0
% 0.12/0.34  #    Propositional unsat core size     : 0
% 0.12/0.34  #    Propositional preprocessing time  : 0.000
% 0.12/0.34  #    Propositional encoding time       : 0.000
% 0.12/0.34  #    Propositional solver time         : 0.000
% 0.12/0.34  #    Success case prop preproc time    : 0.000
% 0.12/0.34  #    Success case prop encoding time   : 0.000
% 0.12/0.34  #    Success case prop solver time     : 0.000
% 0.12/0.34  # Current number of processed clauses  : 16
% 0.12/0.34  #    Positive orientable unit clauses  : 2
% 0.12/0.34  #    Positive unorientable unit clauses: 0
% 0.12/0.34  #    Negative unit clauses             : 2
% 0.12/0.34  #    Non-unit-clauses                  : 12
% 0.12/0.34  # Current number of unprocessed clauses: 6
% 0.12/0.34  # ...number of literals in the above   : 20
% 0.12/0.34  # Current number of archived formulas  : 0
% 0.12/0.34  # Current number of archived clauses   : 12
% 0.12/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.34  # Unit Clause-clause subsumption calls : 1
% 0.12/0.34  # Rewrite failures with RHS unbound    : 0
% 0.12/0.34  # BW rewrite match attempts            : 0
% 0.12/0.34  # BW rewrite match successes           : 0
% 0.12/0.34  # Condensation attempts                : 0
% 0.12/0.34  # Condensation successes               : 0
% 0.12/0.34  # Termbank termtop insertions          : 1176
% 0.12/0.34  
% 0.12/0.34  # -------------------------------------------------
% 0.12/0.34  # User time                : 0.013 s
% 0.12/0.34  # System time              : 0.002 s
% 0.12/0.34  # Total time               : 0.015 s
% 0.12/0.34  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
