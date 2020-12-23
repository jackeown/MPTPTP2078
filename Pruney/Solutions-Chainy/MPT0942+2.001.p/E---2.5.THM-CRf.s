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
% DateTime   : Thu Dec  3 11:00:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   71 (  77 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(t6_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v1_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_wellord2)).

fof(t5_wellord2,axiom,(
    ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

fof(t3_wellord2,axiom,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

fof(t2_wellord2,axiom,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t4_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v6_relat_2(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

fof(t7_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(c_0_8,plain,(
    ! [X2] :
      ( ( v1_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v8_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v4_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v6_relat_2(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( v1_wellord1(X2)
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X2) )
      & ( ~ v1_relat_2(X2)
        | ~ v8_relat_2(X2)
        | ~ v4_relat_2(X2)
        | ~ v6_relat_2(X2)
        | ~ v1_wellord1(X2)
        | v2_wellord1(X2)
        | ~ v1_relat_1(X2) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_9,plain,(
    ! [X8] :
      ( ~ v3_ordinal1(X8)
      | v1_wellord1(k1_wellord2(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_wellord2])])).

fof(c_0_10,plain,(
    ! [X7] : v4_relat_2(k1_wellord2(X7)) ),
    inference(variable_rename,[status(thm)],[t5_wellord2])).

fof(c_0_11,plain,(
    ! [X5] : v8_relat_2(k1_wellord2(X5)) ),
    inference(variable_rename,[status(thm)],[t3_wellord2])).

fof(c_0_12,plain,(
    ! [X4] : v1_relat_2(k1_wellord2(X4)) ),
    inference(variable_rename,[status(thm)],[t2_wellord2])).

fof(c_0_13,plain,(
    ! [X3] : v1_relat_1(k1_wellord2(X3)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_14,plain,(
    ! [X6] :
      ( ~ v3_ordinal1(X6)
      | v6_relat_2(k1_wellord2(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_wellord2])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v2_wellord1(k1_wellord2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t7_wellord2])).

cnf(c_0_16,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( v1_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v4_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v1_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & ~ v2_wellord1(k1_wellord2(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_24,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_wellord1(k1_wellord2(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S084N
% 0.13/0.37  # and selection function SelectCQIArNT.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.13/0.37  fof(t6_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v1_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_wellord2)).
% 0.13/0.37  fof(t5_wellord2, axiom, ![X1]:v4_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_wellord2)).
% 0.13/0.37  fof(t3_wellord2, axiom, ![X1]:v8_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_wellord2)).
% 0.13/0.37  fof(t2_wellord2, axiom, ![X1]:v1_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord2)).
% 0.13/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.13/0.37  fof(t4_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v6_relat_2(k1_wellord2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_wellord2)).
% 0.13/0.37  fof(t7_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 0.13/0.37  fof(c_0_8, plain, ![X2]:((((((v1_relat_2(X2)|~v2_wellord1(X2)|~v1_relat_1(X2))&(v8_relat_2(X2)|~v2_wellord1(X2)|~v1_relat_1(X2)))&(v4_relat_2(X2)|~v2_wellord1(X2)|~v1_relat_1(X2)))&(v6_relat_2(X2)|~v2_wellord1(X2)|~v1_relat_1(X2)))&(v1_wellord1(X2)|~v2_wellord1(X2)|~v1_relat_1(X2)))&(~v1_relat_2(X2)|~v8_relat_2(X2)|~v4_relat_2(X2)|~v6_relat_2(X2)|~v1_wellord1(X2)|v2_wellord1(X2)|~v1_relat_1(X2))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X8]:(~v3_ordinal1(X8)|v1_wellord1(k1_wellord2(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_wellord2])])).
% 0.13/0.37  fof(c_0_10, plain, ![X7]:v4_relat_2(k1_wellord2(X7)), inference(variable_rename,[status(thm)],[t5_wellord2])).
% 0.13/0.37  fof(c_0_11, plain, ![X5]:v8_relat_2(k1_wellord2(X5)), inference(variable_rename,[status(thm)],[t3_wellord2])).
% 0.13/0.37  fof(c_0_12, plain, ![X4]:v1_relat_2(k1_wellord2(X4)), inference(variable_rename,[status(thm)],[t2_wellord2])).
% 0.13/0.37  fof(c_0_13, plain, ![X3]:v1_relat_1(k1_wellord2(X3)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.13/0.37  fof(c_0_14, plain, ![X6]:(~v3_ordinal1(X6)|v6_relat_2(k1_wellord2(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_wellord2])])).
% 0.13/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1)))), inference(assume_negation,[status(cth)],[t7_wellord2])).
% 0.13/0.37  cnf(c_0_16, plain, (v2_wellord1(X1)|~v1_relat_2(X1)|~v8_relat_2(X1)|~v4_relat_2(X1)|~v6_relat_2(X1)|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_17, plain, (v1_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_18, plain, (v4_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_19, plain, (v8_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_20, plain, (v1_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_21, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_22, plain, (v6_relat_2(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_23, negated_conjecture, (v3_ordinal1(esk1_0)&~v2_wellord1(k1_wellord2(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.38  cnf(c_0_24, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~v2_wellord1(k1_wellord2(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 28
% 0.13/0.38  # Proof object clause steps            : 11
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 6
% 0.13/0.38  # Proof object clause conjectures      : 3
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 9
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 2
% 0.13/0.38  # Proof object simplifying inferences  : 7
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 14
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 14
% 0.13/0.38  # Processed clauses                    : 29
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 29
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 3
% 0.13/0.38  # ...of the previous two non-trivial   : 1
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 3
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 15
% 0.13/0.38  #    Positive orientable unit clauses  : 5
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 9
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 14
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 11
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 847
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.030 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
