%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   20 (  50 expanded)
%              Number of clauses        :   13 (  17 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 230 expanded)
%              Number of equality atoms :    7 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t190_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X2,X3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
          & ! [X5] :
              ( m1_subset_1(X5,X2)
             => X1 != k1_funct_1(X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(t17_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
          & ! [X5] :
              ~ ( r2_hidden(X5,X1)
                & k1_funct_1(X4,X5) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
       => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
            & ! [X5] :
                ( m1_subset_1(X5,X2)
               => X1 != k1_funct_1(X4,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t190_funct_2])).

fof(c_0_4,plain,(
    ! [X8,X9,X10,X11] :
      ( ( r2_hidden(esk1_4(X8,X9,X10,X11),X8)
        | ~ r2_hidden(X10,k2_relset_1(X8,X9,X11))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( k1_funct_1(X11,esk1_4(X8,X9,X10,X11)) = X10
        | ~ r2_hidden(X10,k2_relset_1(X8,X9,X11))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_funct_2])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X17] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk3_0,esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & r2_hidden(esk2_0,k2_relset_1(esk3_0,esk4_0,esk5_0))
      & ( ~ m1_subset_1(X17,esk3_0)
        | esk2_0 != k1_funct_1(esk5_0,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | m1_subset_1(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( ~ m1_subset_1(X1,esk3_0)
    | esk2_0 != k1_funct_1(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( k1_funct_1(X1,esk1_4(X2,X3,X4,X1)) = X4
    | ~ r2_hidden(X4,k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_4(esk3_0,esk4_0,X1,esk5_0),esk3_0)
    | ~ r2_hidden(X1,k2_relset_1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,X1,X2)
    | ~ m1_subset_1(esk1_4(X1,X2,esk2_0,esk5_0),esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk2_0,k2_relset_1(X1,X2,esk5_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_9])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relset_1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk1_4(esk3_0,esk4_0,X1,esk5_0),esk3_0)
    | ~ r2_hidden(X1,k2_relset_1(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ m1_subset_1(esk1_4(esk3_0,esk4_0,esk2_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_8]),c_0_10]),c_0_16])])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:12:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050A
% 0.13/0.36  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t190_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 0.13/0.36  fof(t17_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 0.13/0.36  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.36  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5)))))), inference(assume_negation,[status(cth)],[t190_funct_2])).
% 0.13/0.36  fof(c_0_4, plain, ![X8, X9, X10, X11]:((r2_hidden(esk1_4(X8,X9,X10,X11),X8)|~r2_hidden(X10,k2_relset_1(X8,X9,X11))|(~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))&(k1_funct_1(X11,esk1_4(X8,X9,X10,X11))=X10|~r2_hidden(X10,k2_relset_1(X8,X9,X11))|(~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_funct_2])])])])).
% 0.13/0.36  fof(c_0_5, negated_conjecture, ![X17]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r2_hidden(esk2_0,k2_relset_1(esk3_0,esk4_0,esk5_0))&(~m1_subset_1(X17,esk3_0)|esk2_0!=k1_funct_1(esk5_0,X17)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.13/0.36  fof(c_0_6, plain, ![X6, X7]:(~r2_hidden(X6,X7)|m1_subset_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.36  cnf(c_0_7, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|~r2_hidden(X3,k2_relset_1(X1,X2,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_8, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_11, negated_conjecture, (~m1_subset_1(X1,esk3_0)|esk2_0!=k1_funct_1(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_12, plain, (k1_funct_1(X1,esk1_4(X2,X3,X4,X1))=X4|~r2_hidden(X4,k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_13, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_14, negated_conjecture, (r2_hidden(esk1_4(esk3_0,esk4_0,X1,esk5_0),esk3_0)|~r2_hidden(X1,k2_relset_1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10])])).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (~v1_funct_2(esk5_0,X1,X2)|~m1_subset_1(esk1_4(X1,X2,esk2_0,esk5_0),esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk2_0,k2_relset_1(X1,X2,esk5_0))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_9])])])).
% 0.13/0.36  cnf(c_0_16, negated_conjecture, (r2_hidden(esk2_0,k2_relset_1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk1_4(esk3_0,esk4_0,X1,esk5_0),esk3_0)|~r2_hidden(X1,k2_relset_1(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (~m1_subset_1(esk1_4(esk3_0,esk4_0,esk2_0,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_8]), c_0_10]), c_0_16])])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_16]), c_0_18]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 20
% 0.13/0.36  # Proof object clause steps            : 13
% 0.13/0.36  # Proof object formula steps           : 7
% 0.13/0.36  # Proof object conjectures             : 13
% 0.13/0.36  # Proof object clause conjectures      : 10
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 8
% 0.13/0.36  # Proof object initial formulas used   : 3
% 0.13/0.36  # Proof object generating inferences   : 5
% 0.13/0.36  # Proof object simplifying inferences  : 10
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 3
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 8
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 8
% 0.13/0.36  # Processed clauses                    : 21
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 21
% 0.13/0.36  # Other redundant clauses eliminated   : 1
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 7
% 0.13/0.36  # ...of the previous two non-trivial   : 5
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 6
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 1
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 13
% 0.13/0.36  #    Positive orientable unit clauses  : 5
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 7
% 0.13/0.36  # Current number of unprocessed clauses: 0
% 0.13/0.36  # ...number of literals in the above   : 0
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 8
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 46
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 9
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 4
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 846
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.024 s
% 0.13/0.36  # System time              : 0.006 s
% 0.13/0.36  # Total time               : 0.030 s
% 0.13/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
