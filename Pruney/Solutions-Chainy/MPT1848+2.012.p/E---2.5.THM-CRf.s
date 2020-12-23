%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:21 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   21 (  45 expanded)
%              Number of clauses        :   12 (  16 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 160 expanded)
%              Number of equality atoms :   12 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
              & v1_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(l17_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
                & v1_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_tex_2])).

fof(c_0_5,plain,(
    ! [X11,X12] :
      ( ( ~ v1_subset_1(X12,X11)
        | X12 != X11
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) )
      & ( X12 = X11
        | v1_subset_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_6,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | m1_subset_1(u1_struct_0(X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l17_tex_2])])])).

fof(c_0_7,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    & v1_tex_2(esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_tex_2(X8,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
        | X9 != u1_struct_0(X8)
        | v1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk1_2(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))
        | v1_tex_2(X8,X7)
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7) )
      & ( esk1_2(X7,X8) = u1_struct_0(X8)
        | v1_tex_2(X8,X7)
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ v1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | v1_tex_2(X8,X7)
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_9,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12]),c_0_11]),c_0_13])]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.14/0.37  # and selection function SelectNewComplexAHP.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t15_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 0.14/0.37  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.14/0.37  fof(l17_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 0.14/0.37  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.14/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1)))))), inference(assume_negation,[status(cth)],[t15_tex_2])).
% 0.14/0.37  fof(c_0_5, plain, ![X11, X12]:((~v1_subset_1(X12,X11)|X12!=X11|~m1_subset_1(X12,k1_zfmisc_1(X11)))&(X12=X11|v1_subset_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.14/0.37  fof(c_0_6, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|m1_subset_1(u1_struct_0(X14),k1_zfmisc_1(u1_struct_0(X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l17_tex_2])])])).
% 0.14/0.37  fof(c_0_7, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(u1_struct_0(esk3_0)=u1_struct_0(esk2_0)&v1_tex_2(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.37  fof(c_0_8, plain, ![X7, X8, X9]:((~v1_tex_2(X8,X7)|(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))|(X9!=u1_struct_0(X8)|v1_subset_1(X9,u1_struct_0(X7))))|~m1_pre_topc(X8,X7)|~l1_pre_topc(X7))&((m1_subset_1(esk1_2(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))|v1_tex_2(X8,X7)|~m1_pre_topc(X8,X7)|~l1_pre_topc(X7))&((esk1_2(X7,X8)=u1_struct_0(X8)|v1_tex_2(X8,X7)|~m1_pre_topc(X8,X7)|~l1_pre_topc(X7))&(~v1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))|v1_tex_2(X8,X7)|~m1_pre_topc(X8,X7)|~l1_pre_topc(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.14/0.37  cnf(c_0_9, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_10, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_11, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_12, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_14, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_15, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])])).
% 0.14/0.37  cnf(c_0_17, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_10])).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (v1_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (~v1_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_12]), c_0_11]), c_0_13])]), c_0_19]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 21
% 0.14/0.37  # Proof object clause steps            : 12
% 0.14/0.37  # Proof object formula steps           : 9
% 0.14/0.37  # Proof object conjectures             : 10
% 0.14/0.37  # Proof object clause conjectures      : 7
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 7
% 0.14/0.37  # Proof object initial formulas used   : 4
% 0.14/0.37  # Proof object generating inferences   : 4
% 0.14/0.37  # Proof object simplifying inferences  : 10
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 7
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 15
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 15
% 0.14/0.37  # Processed clauses                    : 26
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 1
% 0.14/0.37  # ...remaining for further processing  : 25
% 0.14/0.37  # Other redundant clauses eliminated   : 1
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 25
% 0.14/0.37  # ...of the previous two non-trivial   : 19
% 0.14/0.37  # Contextual simplify-reflections      : 2
% 0.14/0.37  # Paramodulations                      : 22
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 3
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 24
% 0.14/0.37  #    Positive orientable unit clauses  : 6
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 17
% 0.14/0.37  # Current number of unprocessed clauses: 8
% 0.14/0.37  # ...number of literals in the above   : 29
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 0
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 54
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 17
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.37  # Unit Clause-clause subsumption calls : 3
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1584
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
