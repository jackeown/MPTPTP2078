%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:16 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   24 (  43 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 178 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r2_hidden(X3,X1)
         => ( X2 = k1_xboole_0
            | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_funct_2])).

fof(c_0_5,plain,(
    ! [X11,X12,X13,X14] :
      ( ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,X11,X12)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ r2_hidden(X13,X11)
      | X12 = k1_xboole_0
      | r2_hidden(k1_funct_1(X14,X13),k2_relset_1(X11,X12,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

fof(c_0_6,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r2_hidden(esk3_0,esk1_0)
    & esk2_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk4_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | m1_subset_1(k2_relset_1(X8,X9,X10),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_8,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk4_0,X2),k2_relset_1(X3,X1,esk4_0))
    | ~ v1_funct_2(esk4_0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(k2_relset_1(esk1_0,esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),k2_relset_1(esk1_0,esk2_0,esk4_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_12]),c_0_14])]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k2_relset_1(esk1_0,esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,esk3_0),k2_relset_1(esk1_0,esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.28  % Computer   : n008.cluster.edu
% 0.10/0.28  % Model      : x86_64 x86_64
% 0.10/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.28  % Memory     : 8042.1875MB
% 0.10/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.28  % CPULimit   : 60
% 0.10/0.28  % WCLimit    : 600
% 0.10/0.28  % DateTime   : Tue Dec  1 19:47:00 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.29  # Version: 2.5pre002
% 0.10/0.29  # No SInE strategy applied
% 0.10/0.29  # Trying AutoSched0 for 299 seconds
% 0.14/0.32  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.14/0.32  # and selection function SelectCQIAr.
% 0.14/0.32  #
% 0.14/0.32  # Preprocessing time       : 0.027 s
% 0.14/0.32  # Presaturation interreduction done
% 0.14/0.32  
% 0.14/0.32  # Proof found!
% 0.14/0.32  # SZS status Theorem
% 0.14/0.32  # SZS output start CNFRefutation
% 0.14/0.32  fof(t7_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.14/0.32  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 0.14/0.32  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.14/0.32  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.14/0.32  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2))))), inference(assume_negation,[status(cth)],[t7_funct_2])).
% 0.14/0.32  fof(c_0_5, plain, ![X11, X12, X13, X14]:(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|(~r2_hidden(X13,X11)|(X12=k1_xboole_0|r2_hidden(k1_funct_1(X14,X13),k2_relset_1(X11,X12,X14))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.14/0.32  fof(c_0_6, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r2_hidden(esk3_0,esk1_0)&(esk2_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk4_0,esk3_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.32  fof(c_0_7, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|m1_subset_1(k2_relset_1(X8,X9,X10),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.14/0.32  cnf(c_0_8, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.32  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.32  fof(c_0_10, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.14/0.32  cnf(c_0_11, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.32  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.32  cnf(c_0_13, negated_conjecture, (X1=k1_xboole_0|r2_hidden(k1_funct_1(esk4_0,X2),k2_relset_1(X3,X1,esk4_0))|~v1_funct_2(esk4_0,X3,X1)|~r2_hidden(X2,X3)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.32  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.32  cnf(c_0_15, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.32  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.32  cnf(c_0_17, negated_conjecture, (m1_subset_1(k2_relset_1(esk1_0,esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.32  cnf(c_0_18, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),k2_relset_1(esk1_0,esk2_0,esk4_0))|~r2_hidden(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_12]), c_0_14])]), c_0_15])).
% 0.14/0.32  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.32  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,k2_relset_1(esk1_0,esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.32  cnf(c_0_21, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,esk3_0),k2_relset_1(esk1_0,esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.32  cnf(c_0_22, negated_conjecture, (~r2_hidden(k1_funct_1(esk4_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.32  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), ['proof']).
% 0.14/0.32  # SZS output end CNFRefutation
% 0.14/0.32  # Proof object total steps             : 24
% 0.14/0.32  # Proof object clause steps            : 15
% 0.14/0.32  # Proof object formula steps           : 9
% 0.14/0.32  # Proof object conjectures             : 15
% 0.14/0.32  # Proof object clause conjectures      : 12
% 0.14/0.32  # Proof object formula conjectures     : 3
% 0.14/0.32  # Proof object initial clauses used    : 9
% 0.14/0.32  # Proof object initial formulas used   : 4
% 0.14/0.32  # Proof object generating inferences   : 6
% 0.14/0.32  # Proof object simplifying inferences  : 4
% 0.14/0.32  # Training examples: 0 positive, 0 negative
% 0.14/0.32  # Parsed axioms                        : 4
% 0.14/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.32  # Initial clauses                      : 9
% 0.14/0.32  # Removed in clause preprocessing      : 0
% 0.14/0.32  # Initial clauses in saturation        : 9
% 0.14/0.32  # Processed clauses                    : 24
% 0.14/0.32  # ...of these trivial                  : 0
% 0.14/0.32  # ...subsumed                          : 0
% 0.14/0.32  # ...remaining for further processing  : 24
% 0.14/0.32  # Other redundant clauses eliminated   : 0
% 0.14/0.32  # Clauses deleted for lack of memory   : 0
% 0.14/0.32  # Backward-subsumed                    : 0
% 0.14/0.32  # Backward-rewritten                   : 0
% 0.14/0.32  # Generated clauses                    : 7
% 0.14/0.32  # ...of the previous two non-trivial   : 6
% 0.14/0.32  # Contextual simplify-reflections      : 0
% 0.14/0.32  # Paramodulations                      : 7
% 0.14/0.32  # Factorizations                       : 0
% 0.14/0.32  # Equation resolutions                 : 0
% 0.14/0.32  # Propositional unsat checks           : 0
% 0.14/0.32  #    Propositional check models        : 0
% 0.14/0.32  #    Propositional check unsatisfiable : 0
% 0.14/0.32  #    Propositional clauses             : 0
% 0.14/0.32  #    Propositional clauses after purity: 0
% 0.14/0.32  #    Propositional unsat core size     : 0
% 0.14/0.32  #    Propositional preprocessing time  : 0.000
% 0.14/0.32  #    Propositional encoding time       : 0.000
% 0.14/0.32  #    Propositional solver time         : 0.000
% 0.14/0.32  #    Success case prop preproc time    : 0.000
% 0.14/0.32  #    Success case prop encoding time   : 0.000
% 0.14/0.32  #    Success case prop solver time     : 0.000
% 0.14/0.32  # Current number of processed clauses  : 15
% 0.14/0.32  #    Positive orientable unit clauses  : 6
% 0.14/0.32  #    Positive unorientable unit clauses: 0
% 0.14/0.32  #    Negative unit clauses             : 2
% 0.14/0.32  #    Non-unit-clauses                  : 7
% 0.14/0.32  # Current number of unprocessed clauses: 0
% 0.14/0.32  # ...number of literals in the above   : 0
% 0.14/0.32  # Current number of archived formulas  : 0
% 0.14/0.32  # Current number of archived clauses   : 9
% 0.14/0.32  # Clause-clause subsumption calls (NU) : 11
% 0.14/0.32  # Rec. Clause-clause subsumption calls : 11
% 0.14/0.32  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.32  # Unit Clause-clause subsumption calls : 1
% 0.14/0.32  # Rewrite failures with RHS unbound    : 0
% 0.14/0.32  # BW rewrite match attempts            : 0
% 0.14/0.32  # BW rewrite match successes           : 0
% 0.14/0.32  # Condensation attempts                : 0
% 0.14/0.32  # Condensation successes               : 0
% 0.14/0.32  # Termbank termtop insertions          : 843
% 0.14/0.32  
% 0.14/0.32  # -------------------------------------------------
% 0.14/0.32  # User time                : 0.025 s
% 0.14/0.32  # System time              : 0.006 s
% 0.14/0.32  # Total time               : 0.031 s
% 0.14/0.32  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
