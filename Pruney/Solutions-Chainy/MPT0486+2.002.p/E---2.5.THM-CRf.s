%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:27 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   21 (  33 expanded)
%              Number of clauses        :   10 (  14 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 (  89 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_relat_1,conjecture,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t81_relat_1])).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X11,X9)
        | ~ r2_hidden(k4_tarski(X11,X12),X10)
        | X10 != k6_relat_1(X9)
        | ~ v1_relat_1(X10) )
      & ( X11 = X12
        | ~ r2_hidden(k4_tarski(X11,X12),X10)
        | X10 != k6_relat_1(X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X13,X9)
        | X13 != X14
        | r2_hidden(k4_tarski(X13,X14),X10)
        | X10 != k6_relat_1(X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10)),X10)
        | ~ r2_hidden(esk1_2(X9,X10),X9)
        | esk1_2(X9,X10) != esk2_2(X9,X10)
        | X10 = k6_relat_1(X9)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r2_hidden(k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10)),X10)
        | X10 = k6_relat_1(X9)
        | ~ v1_relat_1(X10) )
      & ( esk1_2(X9,X10) = esk2_2(X9,X10)
        | r2_hidden(k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10)),X10)
        | X10 = k6_relat_1(X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X17,X18,X21,X23,X24] :
      ( ( ~ v1_relat_1(X17)
        | ~ r2_hidden(X18,X17)
        | X18 = k4_tarski(esk3_2(X17,X18),esk4_2(X17,X18)) )
      & ( r2_hidden(esk5_1(X21),X21)
        | v1_relat_1(X21) )
      & ( esk5_1(X21) != k4_tarski(X23,X24)
        | v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | k2_xboole_0(k1_tarski(X5),X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_12,negated_conjecture,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X1 = k6_relat_1(X2)
    | r2_hidden(k4_tarski(esk1_2(X2,X1),esk2_2(X2,X1)),X1)
    | r2_hidden(esk1_2(X2,X1),X2)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,plain,(
    ! [X7,X8] : k2_xboole_0(k1_tarski(X7),X8) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k1_xboole_0,k1_xboole_0),esk2_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk5_1(k1_xboole_0),k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13])])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk5_1(k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_18]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_19]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:26:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.12/0.38  # and selection function SelectSmallestOrientable.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t81_relat_1, conjecture, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.12/0.38  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.12/0.38  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.12/0.38  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.12/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.12/0.38  fof(c_0_5, negated_conjecture, ~(k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t81_relat_1])).
% 0.12/0.38  fof(c_0_6, plain, ![X9, X10, X11, X12, X13, X14]:((((r2_hidden(X11,X9)|~r2_hidden(k4_tarski(X11,X12),X10)|X10!=k6_relat_1(X9)|~v1_relat_1(X10))&(X11=X12|~r2_hidden(k4_tarski(X11,X12),X10)|X10!=k6_relat_1(X9)|~v1_relat_1(X10)))&(~r2_hidden(X13,X9)|X13!=X14|r2_hidden(k4_tarski(X13,X14),X10)|X10!=k6_relat_1(X9)|~v1_relat_1(X10)))&((~r2_hidden(k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10)),X10)|(~r2_hidden(esk1_2(X9,X10),X9)|esk1_2(X9,X10)!=esk2_2(X9,X10))|X10=k6_relat_1(X9)|~v1_relat_1(X10))&((r2_hidden(esk1_2(X9,X10),X9)|r2_hidden(k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10)),X10)|X10=k6_relat_1(X9)|~v1_relat_1(X10))&(esk1_2(X9,X10)=esk2_2(X9,X10)|r2_hidden(k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10)),X10)|X10=k6_relat_1(X9)|~v1_relat_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.12/0.38  fof(c_0_7, plain, ![X17, X18, X21, X23, X24]:((~v1_relat_1(X17)|(~r2_hidden(X18,X17)|X18=k4_tarski(esk3_2(X17,X18),esk4_2(X17,X18))))&((r2_hidden(esk5_1(X21),X21)|v1_relat_1(X21))&(esk5_1(X21)!=k4_tarski(X23,X24)|v1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.12/0.38  fof(c_0_8, negated_conjecture, k6_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|X2=k6_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_10, plain, (r2_hidden(esk5_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  fof(c_0_11, plain, ![X5, X6]:(~r2_hidden(X5,X6)|k2_xboole_0(k1_tarski(X5),X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (k6_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_13, plain, (X1=k6_relat_1(X2)|r2_hidden(k4_tarski(esk1_2(X2,X1),esk2_2(X2,X1)),X1)|r2_hidden(esk1_2(X2,X1),X2)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.38  fof(c_0_14, plain, ![X7, X8]:k2_xboole_0(k1_tarski(X7),X8)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.12/0.38  cnf(c_0_15, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k1_xboole_0,k1_xboole_0),esk2_2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk5_1(k1_xboole_0),k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13])])).
% 0.12/0.38  cnf(c_0_17, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk5_1(k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_18]), c_0_17])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_19]), c_0_17]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 21
% 0.12/0.38  # Proof object clause steps            : 10
% 0.12/0.38  # Proof object formula steps           : 11
% 0.12/0.38  # Proof object conjectures             : 8
% 0.12/0.38  # Proof object clause conjectures      : 5
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 5
% 0.12/0.38  # Proof object initial formulas used   : 5
% 0.12/0.38  # Proof object generating inferences   : 5
% 0.12/0.38  # Proof object simplifying inferences  : 4
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 5
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 12
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 12
% 0.12/0.38  # Processed clauses                    : 35
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 35
% 0.12/0.38  # Other redundant clauses eliminated   : 5
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 1
% 0.12/0.38  # Generated clauses                    : 43
% 0.12/0.38  # ...of the previous two non-trivial   : 38
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 39
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 5
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 18
% 0.12/0.38  #    Positive orientable unit clauses  : 1
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 15
% 0.12/0.38  # Current number of unprocessed clauses: 27
% 0.12/0.38  # ...number of literals in the above   : 142
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 14
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 86
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 51
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.38  # Unit Clause-clause subsumption calls : 3
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 1829
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.029 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.033 s
% 0.12/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
