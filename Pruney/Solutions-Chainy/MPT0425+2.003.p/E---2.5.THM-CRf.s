%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:47 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  85 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))
        & ! [X4] :
            ( r2_hidden(X4,X2)
           => r1_xboole_0(X4,X3) ) )
     => r1_tarski(X3,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_setfam_1)).

fof(t98_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))
          & ! [X4] :
              ( r2_hidden(X4,X2)
             => r1_xboole_0(X4,X3) ) )
       => r1_tarski(X3,k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t57_setfam_1])).

fof(c_0_6,negated_conjecture,(
    ! [X18] :
      ( r1_tarski(esk4_0,k3_tarski(k2_xboole_0(esk2_0,esk3_0)))
      & ( ~ r2_hidden(X18,esk3_0)
        | r1_xboole_0(X18,esk4_0) )
      & ~ r1_tarski(esk4_0,k3_tarski(esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_xboole_0(k3_tarski(X12),X13) )
      & ( ~ r1_xboole_0(esk1_2(X12,X13),X13)
        | r1_xboole_0(k3_tarski(X12),X13) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).

cnf(c_0_8,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_11,plain,
    ( r1_xboole_0(k3_tarski(X1),X2)
    | ~ r1_xboole_0(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk1_2(esk3_0,X1),esk4_0)
    | r1_xboole_0(k3_tarski(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,k2_xboole_0(X8,X9))
      | ~ r1_xboole_0(X7,X9)
      | r1_tarski(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(k3_tarski(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_tarski(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X10,X11] : k3_tarski(k2_xboole_0(X10,X11)) = k2_xboole_0(k3_tarski(X10),k3_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk4_0,k2_xboole_0(X1,k3_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(X1))
    | ~ r1_tarski(esk4_0,k3_tarski(k2_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(k2_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:07:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.12/0.36  # and selection function SelectSmallestOrientable.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t57_setfam_1, conjecture, ![X1, X2, X3]:((r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))&![X4]:(r2_hidden(X4,X2)=>r1_xboole_0(X4,X3)))=>r1_tarski(X3,k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_setfam_1)).
% 0.12/0.36  fof(t98_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_xboole_0(X3,X2))=>r1_xboole_0(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 0.12/0.36  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.12/0.36  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.12/0.36  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 0.12/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))&![X4]:(r2_hidden(X4,X2)=>r1_xboole_0(X4,X3)))=>r1_tarski(X3,k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t57_setfam_1])).
% 0.12/0.36  fof(c_0_6, negated_conjecture, ![X18]:((r1_tarski(esk4_0,k3_tarski(k2_xboole_0(esk2_0,esk3_0)))&(~r2_hidden(X18,esk3_0)|r1_xboole_0(X18,esk4_0)))&~r1_tarski(esk4_0,k3_tarski(esk2_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.12/0.36  fof(c_0_7, plain, ![X12, X13]:((r2_hidden(esk1_2(X12,X13),X12)|r1_xboole_0(k3_tarski(X12),X13))&(~r1_xboole_0(esk1_2(X12,X13),X13)|r1_xboole_0(k3_tarski(X12),X13))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).
% 0.12/0.36  cnf(c_0_8, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  fof(c_0_10, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.12/0.36  cnf(c_0_11, plain, (r1_xboole_0(k3_tarski(X1),X2)|~r1_xboole_0(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (r1_xboole_0(esk1_2(esk3_0,X1),esk4_0)|r1_xboole_0(k3_tarski(esk3_0),X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.36  fof(c_0_13, plain, ![X7, X8, X9]:(~r1_tarski(X7,k2_xboole_0(X8,X9))|~r1_xboole_0(X7,X9)|r1_tarski(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.12/0.36  cnf(c_0_14, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (r1_xboole_0(k3_tarski(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.36  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, (r1_xboole_0(esk4_0,k3_tarski(esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.36  fof(c_0_18, plain, ![X10, X11]:k3_tarski(k2_xboole_0(X10,X11))=k2_xboole_0(k3_tarski(X10),k3_tarski(X11)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk4_0,k2_xboole_0(X1,k3_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.36  cnf(c_0_20, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_21, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(X1))|~r1_tarski(esk4_0,k3_tarski(k2_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(k2_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (~r1_tarski(esk4_0,k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 25
% 0.12/0.36  # Proof object clause steps            : 14
% 0.12/0.36  # Proof object formula steps           : 11
% 0.12/0.36  # Proof object conjectures             : 12
% 0.12/0.36  # Proof object clause conjectures      : 9
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 8
% 0.12/0.36  # Proof object initial formulas used   : 5
% 0.12/0.36  # Proof object generating inferences   : 6
% 0.12/0.36  # Proof object simplifying inferences  : 1
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 8
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 8
% 0.12/0.37  # Processed clauses                    : 22
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 22
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 10
% 0.12/0.37  # ...of the previous two non-trivial   : 8
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 10
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 14
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 9
% 0.12/0.37  # Current number of unprocessed clauses: 2
% 0.12/0.37  # ...number of literals in the above   : 5
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 8
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 2
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 752
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.001 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
