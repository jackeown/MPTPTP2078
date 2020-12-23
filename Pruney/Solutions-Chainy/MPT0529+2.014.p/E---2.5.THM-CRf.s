%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:08 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  29 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 (  98 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t129_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t127_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(k3_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t129_relat_1])).

fof(c_0_6,plain,(
    ! [X7,X8,X9] :
      ( ( r1_tarski(esk1_3(X7,X8,X9),X8)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X7,X9)
        | X7 = k3_xboole_0(X8,X9) )
      & ( r1_tarski(esk1_3(X7,X8,X9),X9)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X7,X9)
        | X7 = k3_xboole_0(X8,X9) )
      & ( ~ r1_tarski(esk1_3(X7,X8,X9),X7)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X7,X9)
        | X7 = k3_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | k8_relat_1(X11,k8_relat_1(X12,X13)) = k8_relat_1(k3_xboole_0(X11,X12),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & r1_tarski(esk2_0,esk3_0)
    & k8_relat_1(esk3_0,k8_relat_1(esk2_0,esk4_0)) != k8_relat_1(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k3_xboole_0(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k8_relat_1(k3_xboole_0(X1,X2),esk4_0) = k8_relat_1(X1,k8_relat_1(X2,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k8_relat_1(esk3_0,k8_relat_1(esk2_0,esk4_0)) != k8_relat_1(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:04:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.21/0.39  # and selection function SelectVGNonCR.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.026 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.39  fof(t129_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 0.21/0.39  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 0.21/0.39  fof(t127_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 0.21/0.39  fof(c_0_4, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.39  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3)))), inference(assume_negation,[status(cth)],[t129_relat_1])).
% 0.21/0.39  fof(c_0_6, plain, ![X7, X8, X9]:(((r1_tarski(esk1_3(X7,X8,X9),X8)|(~r1_tarski(X7,X8)|~r1_tarski(X7,X9))|X7=k3_xboole_0(X8,X9))&(r1_tarski(esk1_3(X7,X8,X9),X9)|(~r1_tarski(X7,X8)|~r1_tarski(X7,X9))|X7=k3_xboole_0(X8,X9)))&(~r1_tarski(esk1_3(X7,X8,X9),X7)|(~r1_tarski(X7,X8)|~r1_tarski(X7,X9))|X7=k3_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 0.21/0.39  cnf(c_0_7, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.21/0.39  fof(c_0_8, plain, ![X11, X12, X13]:(~v1_relat_1(X13)|k8_relat_1(X11,k8_relat_1(X12,X13))=k8_relat_1(k3_xboole_0(X11,X12),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).
% 0.21/0.39  fof(c_0_9, negated_conjecture, (v1_relat_1(esk4_0)&(r1_tarski(esk2_0,esk3_0)&k8_relat_1(esk3_0,k8_relat_1(esk2_0,esk4_0))!=k8_relat_1(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.21/0.39  cnf(c_0_10, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_11, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_12, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_13, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k3_xboole_0(X2,X3),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.21/0.39  cnf(c_0_16, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (k8_relat_1(k3_xboole_0(X1,X2),esk4_0)=k8_relat_1(X1,k8_relat_1(X2,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (k8_relat_1(esk3_0,k8_relat_1(esk2_0,esk4_0))!=k8_relat_1(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 21
% 0.21/0.39  # Proof object clause steps            : 12
% 0.21/0.39  # Proof object formula steps           : 9
% 0.21/0.39  # Proof object conjectures             : 9
% 0.21/0.39  # Proof object clause conjectures      : 6
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 7
% 0.21/0.39  # Proof object initial formulas used   : 4
% 0.21/0.39  # Proof object generating inferences   : 4
% 0.21/0.39  # Proof object simplifying inferences  : 4
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 4
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 10
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 10
% 0.21/0.39  # Processed clauses                    : 27
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 26
% 0.21/0.39  # Other redundant clauses eliminated   : 2
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 0
% 0.21/0.39  # Generated clauses                    : 18
% 0.21/0.39  # ...of the previous two non-trivial   : 15
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 16
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 2
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 15
% 0.21/0.39  #    Positive orientable unit clauses  : 6
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 8
% 0.21/0.39  # Current number of unprocessed clauses: 7
% 0.21/0.39  # ...number of literals in the above   : 27
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 9
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 36
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 30
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.39  # Unit Clause-clause subsumption calls : 7
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 11
% 0.21/0.39  # BW rewrite match successes           : 0
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 801
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.027 s
% 0.21/0.39  # System time              : 0.003 s
% 0.21/0.39  # Total time               : 0.030 s
% 0.21/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
