%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:57 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   25 (  35 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  89 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t187_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r1_xboole_0(X2,k1_relat_1(X1))
           => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t187_relat_1])).

fof(c_0_7,plain,(
    ! [X3,X4] :
      ( ~ r1_xboole_0(X3,X4)
      | r1_xboole_0(X4,X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r1_xboole_0(esk2_0,k1_relat_1(esk1_0))
    & k7_relat_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X11] :
      ( ( k1_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k2_relat_1(k7_relat_1(X8,X7)) = k9_relat_1(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k7_relat_1(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( k9_relat_1(X10,X9) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_xboole_0(k1_relat_1(X10),X9)
        | k9_relat_1(X10,X9) = k1_xboole_0
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k9_relat_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( k7_relat_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_20])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n019.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 19:54:22 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  # Version: 2.5pre002
% 0.10/0.32  # No SInE strategy applied
% 0.10/0.32  # Trying AutoSched0 for 299 seconds
% 0.10/0.33  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.10/0.33  # and selection function SelectCQIPrecWNTNp.
% 0.10/0.33  #
% 0.10/0.33  # Preprocessing time       : 0.013 s
% 0.10/0.33  # Presaturation interreduction done
% 0.10/0.33  
% 0.10/0.33  # Proof found!
% 0.10/0.33  # SZS status Theorem
% 0.10/0.33  # SZS output start CNFRefutation
% 0.10/0.33  fof(t187_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.10/0.33  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.10/0.33  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.10/0.33  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.10/0.33  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.10/0.34  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.10/0.34  fof(c_0_6, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t187_relat_1])).
% 0.10/0.34  fof(c_0_7, plain, ![X3, X4]:(~r1_xboole_0(X3,X4)|r1_xboole_0(X4,X3)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.10/0.34  fof(c_0_8, negated_conjecture, (v1_relat_1(esk1_0)&(r1_xboole_0(esk2_0,k1_relat_1(esk1_0))&k7_relat_1(esk1_0,esk2_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.10/0.34  fof(c_0_9, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.10/0.34  fof(c_0_10, plain, ![X7, X8]:(~v1_relat_1(X8)|k2_relat_1(k7_relat_1(X8,X7))=k9_relat_1(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.10/0.34  fof(c_0_11, plain, ![X5, X6]:(~v1_relat_1(X5)|v1_relat_1(k7_relat_1(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.10/0.34  fof(c_0_12, plain, ![X9, X10]:((k9_relat_1(X10,X9)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_xboole_0(k1_relat_1(X10),X9)|k9_relat_1(X10,X9)=k1_xboole_0|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.10/0.34  cnf(c_0_13, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.10/0.34  cnf(c_0_14, negated_conjecture, (r1_xboole_0(esk2_0,k1_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.10/0.34  cnf(c_0_15, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.10/0.34  cnf(c_0_16, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.10/0.34  cnf(c_0_17, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.10/0.34  cnf(c_0_18, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.34  cnf(c_0_19, negated_conjecture, (r1_xboole_0(k1_relat_1(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.10/0.34  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.10/0.34  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=k1_xboole_0|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.10/0.34  cnf(c_0_22, negated_conjecture, (k9_relat_1(esk1_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.10/0.34  cnf(c_0_23, negated_conjecture, (k7_relat_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.10/0.34  cnf(c_0_24, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_20])]), c_0_23]), ['proof']).
% 0.10/0.34  # SZS output end CNFRefutation
% 0.10/0.34  # Proof object total steps             : 25
% 0.10/0.34  # Proof object clause steps            : 12
% 0.10/0.34  # Proof object formula steps           : 13
% 0.10/0.34  # Proof object conjectures             : 9
% 0.10/0.34  # Proof object clause conjectures      : 6
% 0.10/0.34  # Proof object formula conjectures     : 3
% 0.10/0.34  # Proof object initial clauses used    : 8
% 0.10/0.34  # Proof object initial formulas used   : 6
% 0.10/0.34  # Proof object generating inferences   : 4
% 0.10/0.34  # Proof object simplifying inferences  : 6
% 0.10/0.34  # Training examples: 0 positive, 0 negative
% 0.10/0.34  # Parsed axioms                        : 6
% 0.10/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.34  # Initial clauses                      : 10
% 0.10/0.34  # Removed in clause preprocessing      : 0
% 0.10/0.34  # Initial clauses in saturation        : 10
% 0.10/0.34  # Processed clauses                    : 23
% 0.10/0.34  # ...of these trivial                  : 0
% 0.10/0.34  # ...subsumed                          : 0
% 0.10/0.34  # ...remaining for further processing  : 23
% 0.10/0.34  # Other redundant clauses eliminated   : 0
% 0.10/0.34  # Clauses deleted for lack of memory   : 0
% 0.10/0.34  # Backward-subsumed                    : 0
% 0.10/0.34  # Backward-rewritten                   : 0
% 0.10/0.34  # Generated clauses                    : 6
% 0.10/0.34  # ...of the previous two non-trivial   : 3
% 0.10/0.34  # Contextual simplify-reflections      : 1
% 0.10/0.34  # Paramodulations                      : 6
% 0.10/0.34  # Factorizations                       : 0
% 0.10/0.34  # Equation resolutions                 : 0
% 0.10/0.34  # Propositional unsat checks           : 0
% 0.10/0.34  #    Propositional check models        : 0
% 0.10/0.34  #    Propositional check unsatisfiable : 0
% 0.10/0.34  #    Propositional clauses             : 0
% 0.10/0.34  #    Propositional clauses after purity: 0
% 0.10/0.34  #    Propositional unsat core size     : 0
% 0.10/0.34  #    Propositional preprocessing time  : 0.000
% 0.10/0.34  #    Propositional encoding time       : 0.000
% 0.10/0.34  #    Propositional solver time         : 0.000
% 0.10/0.34  #    Success case prop preproc time    : 0.000
% 0.10/0.34  #    Success case prop encoding time   : 0.000
% 0.10/0.34  #    Success case prop solver time     : 0.000
% 0.10/0.34  # Current number of processed clauses  : 13
% 0.10/0.34  #    Positive orientable unit clauses  : 4
% 0.10/0.34  #    Positive unorientable unit clauses: 0
% 0.10/0.34  #    Negative unit clauses             : 1
% 0.10/0.34  #    Non-unit-clauses                  : 8
% 0.10/0.34  # Current number of unprocessed clauses: 0
% 0.10/0.34  # ...number of literals in the above   : 0
% 0.10/0.34  # Current number of archived formulas  : 0
% 0.10/0.34  # Current number of archived clauses   : 10
% 0.10/0.34  # Clause-clause subsumption calls (NU) : 2
% 0.10/0.34  # Rec. Clause-clause subsumption calls : 2
% 0.10/0.34  # Non-unit clause-clause subsumptions  : 1
% 0.10/0.34  # Unit Clause-clause subsumption calls : 0
% 0.10/0.34  # Rewrite failures with RHS unbound    : 0
% 0.10/0.34  # BW rewrite match attempts            : 0
% 0.10/0.34  # BW rewrite match successes           : 0
% 0.10/0.34  # Condensation attempts                : 0
% 0.10/0.34  # Condensation successes               : 0
% 0.10/0.34  # Termbank termtop insertions          : 699
% 0.10/0.34  
% 0.10/0.34  # -------------------------------------------------
% 0.10/0.34  # User time                : 0.013 s
% 0.10/0.34  # System time              : 0.003 s
% 0.10/0.34  # Total time               : 0.016 s
% 0.10/0.34  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
