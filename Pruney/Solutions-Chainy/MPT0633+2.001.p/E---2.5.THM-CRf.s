%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   19 (  27 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 (  96 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(t35_funct_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X5)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( X7 = X8
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X9,X5)
        | X9 != X10
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(esk1_2(X5,X6),X5)
        | esk1_2(X5,X6) != esk2_2(X5,X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( esk1_2(X5,X6) = esk2_2(X5,X6)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    inference(assume_negation,[status(cth)],[t35_funct_1])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    & k1_funct_1(k6_relat_1(esk4_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | X2 != k6_relat_1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X13] :
      ( v1_relat_1(k6_relat_1(X13))
      & v1_funct_1(k6_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_11,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(X14,k1_relat_1(X16))
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X15 = k1_funct_1(X16,X14)
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X14,k1_relat_1(X16))
        | X15 != k1_funct_1(X16,X14)
        | r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk3_0),X1)
    | X1 != k6_relat_1(esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk3_0),k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])])).

cnf(c_0_16,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(k6_relat_1(esk4_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_13])]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.19/0.37  # and selection function SelectDiffNegLit.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.19/0.37  fof(t35_funct_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k1_funct_1(k6_relat_1(X2),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 0.19/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.37  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.37  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10]:((((r2_hidden(X7,X5)|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6))&(X7=X8|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&(~r2_hidden(X9,X5)|X9!=X10|r2_hidden(k4_tarski(X9,X10),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|(~r2_hidden(esk1_2(X5,X6),X5)|esk1_2(X5,X6)!=esk2_2(X5,X6))|X6=k6_relat_1(X5)|~v1_relat_1(X6))&((r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))&(esk1_2(X5,X6)=esk2_2(X5,X6)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k1_funct_1(k6_relat_1(X2),X1)=X1)), inference(assume_negation,[status(cth)],[t35_funct_1])).
% 0.19/0.37  cnf(c_0_6, plain, (r2_hidden(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)|X1!=X3|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, (r2_hidden(esk3_0,esk4_0)&k1_funct_1(k6_relat_1(esk4_0),esk3_0)!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.37  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X1,X1),X2)|X2!=k6_relat_1(X3)|~r2_hidden(X1,X3)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_9, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_10, plain, ![X13]:(v1_relat_1(k6_relat_1(X13))&v1_funct_1(k6_relat_1(X13))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.37  fof(c_0_11, plain, ![X14, X15, X16]:(((r2_hidden(X14,k1_relat_1(X16))|~r2_hidden(k4_tarski(X14,X15),X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(X15=k1_funct_1(X16,X14)|~r2_hidden(k4_tarski(X14,X15),X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X14,k1_relat_1(X16))|X15!=k1_funct_1(X16,X14)|r2_hidden(k4_tarski(X14,X15),X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk3_0),X1)|X1!=k6_relat_1(esk4_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.37  cnf(c_0_13, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_14, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk3_0),k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])])).
% 0.19/0.37  cnf(c_0_16, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (k1_funct_1(k6_relat_1(esk4_0),esk3_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_13])]), c_0_17]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 19
% 0.19/0.37  # Proof object clause steps            : 10
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 8
% 0.19/0.37  # Proof object clause conjectures      : 5
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 6
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 3
% 0.19/0.37  # Proof object simplifying inferences  : 7
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 13
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 13
% 0.19/0.37  # Processed clauses                    : 29
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 29
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 9
% 0.19/0.37  # ...of the previous two non-trivial   : 8
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 7
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 15
% 0.19/0.37  #    Positive orientable unit clauses  : 4
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 10
% 0.19/0.37  # Current number of unprocessed clauses: 2
% 0.19/0.37  # ...number of literals in the above   : 6
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 13
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 19
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 2
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1231
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
