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
% DateTime   : Thu Dec  3 10:31:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  46 expanded)
%              Number of clauses        :   14 (  23 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 256 expanded)
%              Number of equality atoms :   24 (  84 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t5_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_3,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_4,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_5,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t5_xboole_1])).

cnf(c_0_7,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_5])).

fof(c_0_11,negated_conjecture,(
    k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0) != k2_xboole_0(k2_xboole_0(esk2_0,esk4_0),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0) != k2_xboole_0(k2_xboole_0(esk2_0,esk4_0),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))) != k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.20/0.55  # and selection function SelectVGNonCR.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.026 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.55  fof(t5_xboole_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_1)).
% 0.20/0.55  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.55  fof(c_0_3, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.55  cnf(c_0_4, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.55  cnf(c_0_5, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.55  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t5_xboole_1])).
% 0.20/0.55  cnf(c_0_7, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.55  cnf(c_0_8, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_4])).
% 0.20/0.55  cnf(c_0_9, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.55  cnf(c_0_10, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_5])).
% 0.20/0.55  fof(c_0_11, negated_conjecture, k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0)!=k2_xboole_0(k2_xboole_0(esk2_0,esk4_0),k2_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.55  fof(c_0_12, plain, ![X14, X15, X16]:k2_xboole_0(k2_xboole_0(X14,X15),X16)=k2_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.55  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.20/0.55  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 0.20/0.55  cnf(c_0_15, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk4_0)!=k2_xboole_0(k2_xboole_0(esk2_0,esk4_0),k2_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.55  cnf(c_0_16, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.55  cnf(c_0_17, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r2_hidden(esk1_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.55  cnf(c_0_18, negated_conjecture, (k2_xboole_0(esk2_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))!=k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.20/0.55  cnf(c_0_19, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.20/0.55  cnf(c_0_20, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])]), ['proof']).
% 0.20/0.55  # SZS output end CNFRefutation
% 0.20/0.55  # Proof object total steps             : 21
% 0.20/0.55  # Proof object clause steps            : 14
% 0.20/0.55  # Proof object formula steps           : 7
% 0.20/0.55  # Proof object conjectures             : 6
% 0.20/0.55  # Proof object clause conjectures      : 3
% 0.20/0.55  # Proof object formula conjectures     : 3
% 0.20/0.55  # Proof object initial clauses used    : 6
% 0.20/0.55  # Proof object initial formulas used   : 3
% 0.20/0.55  # Proof object generating inferences   : 6
% 0.20/0.55  # Proof object simplifying inferences  : 5
% 0.20/0.55  # Training examples: 0 positive, 0 negative
% 0.20/0.55  # Parsed axioms                        : 3
% 0.20/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.55  # Initial clauses                      : 8
% 0.20/0.55  # Removed in clause preprocessing      : 0
% 0.20/0.55  # Initial clauses in saturation        : 8
% 0.20/0.55  # Processed clauses                    : 1673
% 0.20/0.55  # ...of these trivial                  : 58
% 0.20/0.55  # ...subsumed                          : 1378
% 0.20/0.55  # ...remaining for further processing  : 237
% 0.20/0.55  # Other redundant clauses eliminated   : 6
% 0.20/0.55  # Clauses deleted for lack of memory   : 0
% 0.20/0.55  # Backward-subsumed                    : 6
% 0.20/0.55  # Backward-rewritten                   : 29
% 0.20/0.55  # Generated clauses                    : 15670
% 0.20/0.55  # ...of the previous two non-trivial   : 14814
% 0.20/0.55  # Contextual simplify-reflections      : 10
% 0.20/0.55  # Paramodulations                      : 15437
% 0.20/0.55  # Factorizations                       : 188
% 0.20/0.55  # Equation resolutions                 : 45
% 0.20/0.55  # Propositional unsat checks           : 0
% 0.20/0.55  #    Propositional check models        : 0
% 0.20/0.55  #    Propositional check unsatisfiable : 0
% 0.20/0.55  #    Propositional clauses             : 0
% 0.20/0.55  #    Propositional clauses after purity: 0
% 0.20/0.55  #    Propositional unsat core size     : 0
% 0.20/0.55  #    Propositional preprocessing time  : 0.000
% 0.20/0.55  #    Propositional encoding time       : 0.000
% 0.20/0.55  #    Propositional solver time         : 0.000
% 0.20/0.55  #    Success case prop preproc time    : 0.000
% 0.20/0.55  #    Success case prop encoding time   : 0.000
% 0.20/0.55  #    Success case prop solver time     : 0.000
% 0.20/0.55  # Current number of processed clauses  : 194
% 0.20/0.55  #    Positive orientable unit clauses  : 10
% 0.20/0.55  #    Positive unorientable unit clauses: 0
% 0.20/0.55  #    Negative unit clauses             : 0
% 0.20/0.55  #    Non-unit-clauses                  : 184
% 0.20/0.55  # Current number of unprocessed clauses: 13109
% 0.20/0.55  # ...number of literals in the above   : 48319
% 0.20/0.55  # Current number of archived formulas  : 0
% 0.20/0.55  # Current number of archived clauses   : 43
% 0.20/0.55  # Clause-clause subsumption calls (NU) : 27113
% 0.20/0.55  # Rec. Clause-clause subsumption calls : 23029
% 0.20/0.55  # Non-unit clause-clause subsumptions  : 1394
% 0.20/0.55  # Unit Clause-clause subsumption calls : 140
% 0.20/0.55  # Rewrite failures with RHS unbound    : 0
% 0.20/0.55  # BW rewrite match attempts            : 232
% 0.20/0.55  # BW rewrite match successes           : 11
% 0.20/0.55  # Condensation attempts                : 0
% 0.20/0.55  # Condensation successes               : 0
% 0.20/0.55  # Termbank termtop insertions          : 377369
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.206 s
% 0.20/0.56  # System time              : 0.009 s
% 0.20/0.56  # Total time               : 0.215 s
% 0.20/0.56  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
