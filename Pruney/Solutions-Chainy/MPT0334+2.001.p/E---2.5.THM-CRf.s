%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:37 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  57 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t147_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( X1 != X2
     => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_5,plain,(
    ! [X57,X58,X59,X60,X61,X62] :
      ( ( ~ r2_hidden(X59,X58)
        | X59 = X57
        | X58 != k1_tarski(X57) )
      & ( X60 != X57
        | r2_hidden(X60,X58)
        | X58 != k1_tarski(X57) )
      & ( ~ r2_hidden(esk4_2(X61,X62),X62)
        | esk4_2(X61,X62) != X61
        | X62 = k1_tarski(X61) )
      & ( r2_hidden(esk4_2(X61,X62),X62)
        | esk4_2(X61,X62) = X61
        | X62 = k1_tarski(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( X1 != X2
       => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t147_zfmisc_1])).

cnf(c_0_7,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X76,X77] :
      ( ( k4_xboole_0(X76,k1_tarski(X77)) != X76
        | ~ r2_hidden(X77,X76) )
      & ( r2_hidden(X77,X76)
        | k4_xboole_0(X76,k1_tarski(X77)) = X76 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_9,negated_conjecture,
    ( esk5_0 != esk6_0
    & k4_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)) != k2_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk6_0)),k1_tarski(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_11,plain,(
    ! [X43,X44,X45] : k4_xboole_0(k2_xboole_0(X43,X44),X45) = k2_xboole_0(k4_xboole_0(X43,X45),k4_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)) != k2_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk6_0)),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    | X2 = X1 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),k4_xboole_0(esk7_0,k1_tarski(esk6_0))) != k4_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X3))) = k4_xboole_0(k2_xboole_0(k1_tarski(X1),X2),k1_tarski(X3))
    | X3 = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.20/0.44  # and selection function SelectUnlessUniqMax.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.029 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.44  fof(t147_zfmisc_1, conjecture, ![X1, X2, X3]:(X1!=X2=>k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2))=k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 0.20/0.44  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.44  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.44  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.20/0.44  fof(c_0_5, plain, ![X57, X58, X59, X60, X61, X62]:(((~r2_hidden(X59,X58)|X59=X57|X58!=k1_tarski(X57))&(X60!=X57|r2_hidden(X60,X58)|X58!=k1_tarski(X57)))&((~r2_hidden(esk4_2(X61,X62),X62)|esk4_2(X61,X62)!=X61|X62=k1_tarski(X61))&(r2_hidden(esk4_2(X61,X62),X62)|esk4_2(X61,X62)=X61|X62=k1_tarski(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.44  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(X1!=X2=>k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2))=k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)))), inference(assume_negation,[status(cth)],[t147_zfmisc_1])).
% 0.20/0.44  cnf(c_0_7, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.44  fof(c_0_8, plain, ![X76, X77]:((k4_xboole_0(X76,k1_tarski(X77))!=X76|~r2_hidden(X77,X76))&(r2_hidden(X77,X76)|k4_xboole_0(X76,k1_tarski(X77))=X76)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.44  fof(c_0_9, negated_conjecture, (esk5_0!=esk6_0&k4_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0))!=k2_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk6_0)),k1_tarski(esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.44  fof(c_0_10, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.44  fof(c_0_11, plain, ![X43, X44, X45]:k4_xboole_0(k2_xboole_0(X43,X44),X45)=k2_xboole_0(k4_xboole_0(X43,X45),k4_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.20/0.44  cnf(c_0_12, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_7])).
% 0.20/0.44  cnf(c_0_13, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_14, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0))!=k2_xboole_0(k4_xboole_0(esk7_0,k1_tarski(esk6_0)),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.44  cnf(c_0_16, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.44  cnf(c_0_17, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)|X2=X1), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.44  cnf(c_0_18, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),k4_xboole_0(esk7_0,k1_tarski(esk6_0)))!=k4_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk5_0)),k1_tarski(esk6_0))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.44  cnf(c_0_19, plain, (k2_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X3)))=k4_xboole_0(k2_xboole_0(k1_tarski(X1),X2),k1_tarski(X3))|X3=X1), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.44  cnf(c_0_20, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_21, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15])]), c_0_20]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 22
% 0.20/0.44  # Proof object clause steps            : 11
% 0.20/0.44  # Proof object formula steps           : 11
% 0.20/0.44  # Proof object conjectures             : 7
% 0.20/0.44  # Proof object clause conjectures      : 4
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 6
% 0.20/0.44  # Proof object initial formulas used   : 5
% 0.20/0.44  # Proof object generating inferences   : 3
% 0.20/0.44  # Proof object simplifying inferences  : 5
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 23
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 45
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 45
% 0.20/0.44  # Processed clauses                    : 776
% 0.20/0.44  # ...of these trivial                  : 26
% 0.20/0.44  # ...subsumed                          : 486
% 0.20/0.44  # ...remaining for further processing  : 264
% 0.20/0.44  # Other redundant clauses eliminated   : 12
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 1
% 0.20/0.44  # Backward-rewritten                   : 30
% 0.20/0.44  # Generated clauses                    : 3935
% 0.20/0.44  # ...of the previous two non-trivial   : 3129
% 0.20/0.44  # Contextual simplify-reflections      : 1
% 0.20/0.44  # Paramodulations                      : 3914
% 0.20/0.44  # Factorizations                       : 10
% 0.20/0.44  # Equation resolutions                 : 12
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 179
% 0.20/0.44  #    Positive orientable unit clauses  : 46
% 0.20/0.44  #    Positive unorientable unit clauses: 4
% 0.20/0.44  #    Negative unit clauses             : 41
% 0.20/0.44  #    Non-unit-clauses                  : 88
% 0.20/0.44  # Current number of unprocessed clauses: 2379
% 0.20/0.44  # ...number of literals in the above   : 4627
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 74
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 678
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 601
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 67
% 0.20/0.44  # Unit Clause-clause subsumption calls : 265
% 0.20/0.44  # Rewrite failures with RHS unbound    : 46
% 0.20/0.44  # BW rewrite match attempts            : 485
% 0.20/0.44  # BW rewrite match successes           : 111
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 44688
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.087 s
% 0.20/0.44  # System time              : 0.005 s
% 0.20/0.44  # Total time               : 0.092 s
% 0.20/0.44  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
