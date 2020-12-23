%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:16 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  32 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_finset_1(u1_struct_0(X1))
       => v1_compts_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_compts_1)).

fof(fc9_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v8_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_finset_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_struct_0)).

fof(cc3_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( v8_struct_0(X1)
          & v2_pre_topc(X1) )
       => ( v2_pre_topc(X1)
          & v1_compts_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_compts_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_finset_1(u1_struct_0(X1))
         => v1_compts_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t27_compts_1])).

fof(c_0_5,plain,(
    ! [X3] :
      ( v8_struct_0(X3)
      | ~ l1_struct_0(X3)
      | ~ v1_finset_1(u1_struct_0(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_struct_0])])])).

fof(c_0_6,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & v1_finset_1(u1_struct_0(esk1_0))
    & ~ v1_compts_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X4] :
      ( ( v2_pre_topc(X4)
        | ~ v8_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( v1_compts_1(X4)
        | ~ v8_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_compts_1])])])).

cnf(c_0_8,plain,
    ( v8_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_finset_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_finset_1(u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_compts_1(X1)
    | ~ v8_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v8_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_15,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | l1_struct_0(X2) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_16,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t27_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_finset_1(u1_struct_0(X1))=>v1_compts_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_compts_1)).
% 0.21/0.38  fof(fc9_struct_0, axiom, ![X1]:((~(v8_struct_0(X1))&l1_struct_0(X1))=>~(v1_finset_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_struct_0)).
% 0.21/0.38  fof(cc3_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>((v8_struct_0(X1)&v2_pre_topc(X1))=>(v2_pre_topc(X1)&v1_compts_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_compts_1)).
% 0.21/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.38  fof(c_0_4, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_finset_1(u1_struct_0(X1))=>v1_compts_1(X1)))), inference(assume_negation,[status(cth)],[t27_compts_1])).
% 0.21/0.38  fof(c_0_5, plain, ![X3]:(v8_struct_0(X3)|~l1_struct_0(X3)|~v1_finset_1(u1_struct_0(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_struct_0])])])).
% 0.21/0.38  fof(c_0_6, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(v1_finset_1(u1_struct_0(esk1_0))&~v1_compts_1(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.21/0.38  fof(c_0_7, plain, ![X4]:((v2_pre_topc(X4)|(~v8_struct_0(X4)|~v2_pre_topc(X4))|~l1_pre_topc(X4))&(v1_compts_1(X4)|(~v8_struct_0(X4)|~v2_pre_topc(X4))|~l1_pre_topc(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_compts_1])])])).
% 0.21/0.38  cnf(c_0_8, plain, (v8_struct_0(X1)|~l1_struct_0(X1)|~v1_finset_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.38  cnf(c_0_9, negated_conjecture, (v1_finset_1(u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.38  cnf(c_0_10, plain, (v1_compts_1(X1)|~v8_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  cnf(c_0_11, negated_conjecture, (v8_struct_0(esk1_0)|~l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.21/0.38  cnf(c_0_12, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.38  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.38  cnf(c_0_14, negated_conjecture, (~v1_compts_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.38  fof(c_0_15, plain, ![X2]:(~l1_pre_topc(X2)|l1_struct_0(X2)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.38  cnf(c_0_16, negated_conjecture, (~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.21/0.38  cnf(c_0_17, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_13])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 19
% 0.21/0.38  # Proof object clause steps            : 10
% 0.21/0.38  # Proof object formula steps           : 9
% 0.21/0.38  # Proof object conjectures             : 10
% 0.21/0.38  # Proof object clause conjectures      : 7
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 7
% 0.21/0.38  # Proof object initial formulas used   : 4
% 0.21/0.38  # Proof object generating inferences   : 3
% 0.21/0.38  # Proof object simplifying inferences  : 6
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 4
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 8
% 0.21/0.38  # Removed in clause preprocessing      : 1
% 0.21/0.38  # Initial clauses in saturation        : 7
% 0.21/0.38  # Processed clauses                    : 16
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 16
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 0
% 0.21/0.38  # Generated clauses                    : 3
% 0.21/0.38  # ...of the previous two non-trivial   : 2
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 3
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 9
% 0.21/0.38  #    Positive orientable unit clauses  : 3
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 4
% 0.21/0.38  # Current number of unprocessed clauses: 0
% 0.21/0.38  # ...number of literals in the above   : 0
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 7
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 4
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 4
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.38  # Unit Clause-clause subsumption calls : 3
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 0
% 0.21/0.38  # BW rewrite match successes           : 0
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 470
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.024 s
% 0.21/0.38  # System time              : 0.007 s
% 0.21/0.38  # Total time               : 0.031 s
% 0.21/0.38  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
