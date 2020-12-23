%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  35 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   86 ( 194 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r4_wellord1(X1,X2)
              & v2_wellord1(X1) )
           => v2_wellord1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).

fof(t54_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( v2_wellord1(X1)
                  & r3_wellord1(X1,X2,X3) )
               => v2_wellord1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

fof(d8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
          <=> ? [X3] :
                ( v1_relat_1(X3)
                & v1_funct_1(X3)
                & r3_wellord1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r4_wellord1(X1,X2)
                & v2_wellord1(X1) )
             => v2_wellord1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_wellord1])).

fof(c_0_4,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v2_wellord1(X8)
      | ~ r3_wellord1(X8,X9,X10)
      | v2_wellord1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_wellord1])])])).

fof(c_0_5,plain,(
    ! [X4,X5,X7] :
      ( ( v1_relat_1(esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( v1_funct_1(esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( r3_wellord1(X4,X5,esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ r3_wellord1(X4,X5,X7)
        | r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r4_wellord1(esk2_0,esk3_0)
    & v2_wellord1(esk2_0)
    & ~ v2_wellord1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( v2_wellord1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v2_wellord1(X1)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r3_wellord1(X1,X2,esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_funct_1(esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_wellord1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v2_wellord1(X1)
    | ~ v2_wellord1(X2)
    | ~ r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_wellord1(X1)
    | ~ r4_wellord1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_15,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r4_wellord1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02FN
% 0.20/0.37  # and selection function PSelectNonAntiRROptimalLit.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t65_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((r4_wellord1(X1,X2)&v2_wellord1(X1))=>v2_wellord1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_wellord1)).
% 0.20/0.37  fof(t54_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((v2_wellord1(X1)&r3_wellord1(X1,X2,X3))=>v2_wellord1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_wellord1)).
% 0.20/0.37  fof(d8_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)<=>?[X3]:((v1_relat_1(X3)&v1_funct_1(X3))&r3_wellord1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_wellord1)).
% 0.20/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((r4_wellord1(X1,X2)&v2_wellord1(X1))=>v2_wellord1(X2))))), inference(assume_negation,[status(cth)],[t65_wellord1])).
% 0.20/0.37  fof(c_0_4, plain, ![X8, X9, X10]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|(~v1_relat_1(X10)|~v1_funct_1(X10)|(~v2_wellord1(X8)|~r3_wellord1(X8,X9,X10)|v2_wellord1(X9))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_wellord1])])])).
% 0.20/0.37  fof(c_0_5, plain, ![X4, X5, X7]:((((v1_relat_1(esk1_2(X4,X5))|~r4_wellord1(X4,X5)|~v1_relat_1(X5)|~v1_relat_1(X4))&(v1_funct_1(esk1_2(X4,X5))|~r4_wellord1(X4,X5)|~v1_relat_1(X5)|~v1_relat_1(X4)))&(r3_wellord1(X4,X5,esk1_2(X4,X5))|~r4_wellord1(X4,X5)|~v1_relat_1(X5)|~v1_relat_1(X4)))&(~v1_relat_1(X7)|~v1_funct_1(X7)|~r3_wellord1(X4,X5,X7)|r4_wellord1(X4,X5)|~v1_relat_1(X5)|~v1_relat_1(X4))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).
% 0.20/0.37  fof(c_0_6, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&((r4_wellord1(esk2_0,esk3_0)&v2_wellord1(esk2_0))&~v2_wellord1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.20/0.37  cnf(c_0_7, plain, (v2_wellord1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v2_wellord1(X1)|~r3_wellord1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.37  cnf(c_0_8, plain, (r3_wellord1(X1,X2,esk1_2(X1,X2))|~r4_wellord1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_9, plain, (v1_relat_1(esk1_2(X1,X2))|~r4_wellord1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_10, plain, (v1_funct_1(esk1_2(X1,X2))|~r4_wellord1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (~v2_wellord1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_12, plain, (v2_wellord1(X1)|~v2_wellord1(X2)|~r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (~v2_wellord1(X1)|~r4_wellord1(X1,esk3_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (r4_wellord1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 19
% 0.20/0.37  # Proof object clause steps            : 12
% 0.20/0.37  # Proof object formula steps           : 7
% 0.20/0.37  # Proof object conjectures             : 10
% 0.20/0.37  # Proof object clause conjectures      : 7
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 9
% 0.20/0.37  # Proof object initial formulas used   : 3
% 0.20/0.37  # Proof object generating inferences   : 3
% 0.20/0.37  # Proof object simplifying inferences  : 7
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 3
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 10
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 10
% 0.20/0.37  # Processed clauses                    : 22
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 22
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 7
% 0.20/0.37  # ...of the previous two non-trivial   : 4
% 0.20/0.37  # Contextual simplify-reflections      : 2
% 0.20/0.37  # Paramodulations                      : 7
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 12
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 7
% 0.20/0.37  # Current number of unprocessed clauses: 2
% 0.20/0.37  # ...number of literals in the above   : 10
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 10
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 5
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 922
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.028 s
% 0.20/0.37  # System time              : 0.003 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
