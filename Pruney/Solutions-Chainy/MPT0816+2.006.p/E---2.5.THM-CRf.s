%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:05 EST 2020

% Result     : Theorem 0.33s
% Output     : CNFRefutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   28 (  48 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 141 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ( r1_tarski(X1,X4)
       => m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t11_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(c_0_5,plain,(
    ! [X11,X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ r1_tarski(X11,X14)
      | m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).

fof(c_0_6,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_7,plain,
    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X7))
        | ~ r1_tarski(X5,X6) )
      & ( r1_tarski(k2_zfmisc_1(X7,X5),k2_zfmisc_1(X7,X6))
        | ~ r1_tarski(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X10] :
      ( ~ v1_relat_1(X10)
      | r1_tarski(X10,k2_zfmisc_1(k1_relat_1(X10),k2_relat_1(X10))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( r1_tarski(k1_relat_1(X3),X1)
            & r1_tarski(k2_relat_1(X3),X2) )
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t11_relset_1])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(k1_relat_1(esk3_0),esk1_0)
    & r1_tarski(k2_relat_1(esk3_0),esk2_0)
    & ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X3))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.33/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.33/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.33/0.52  #
% 0.33/0.52  # Preprocessing time       : 0.037 s
% 0.33/0.52  # Presaturation interreduction done
% 0.33/0.52  
% 0.33/0.52  # Proof found!
% 0.33/0.52  # SZS status Theorem
% 0.33/0.52  # SZS output start CNFRefutation
% 0.33/0.52  fof(t4_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>(r1_tarski(X1,X4)=>m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 0.33/0.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.33/0.52  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.33/0.52  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.33/0.52  fof(t11_relset_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.33/0.52  fof(c_0_5, plain, ![X11, X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|(~r1_tarski(X11,X14)|m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).
% 0.33/0.52  fof(c_0_6, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.33/0.52  cnf(c_0_7, plain, (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.33/0.52  cnf(c_0_8, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.33/0.52  fof(c_0_9, plain, ![X5, X6, X7]:((r1_tarski(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X7))|~r1_tarski(X5,X6))&(r1_tarski(k2_zfmisc_1(X7,X5),k2_zfmisc_1(X7,X6))|~r1_tarski(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.33/0.52  cnf(c_0_10, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X4,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.33/0.52  cnf(c_0_11, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.33/0.52  fof(c_0_12, plain, ![X10]:(~v1_relat_1(X10)|r1_tarski(X10,k2_zfmisc_1(k1_relat_1(X10),k2_relat_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.33/0.52  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.33/0.52  cnf(c_0_14, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.33/0.52  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t11_relset_1])).
% 0.33/0.52  cnf(c_0_16, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.33/0.52  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.33/0.52  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.33/0.52  fof(c_0_19, negated_conjecture, (v1_relat_1(esk3_0)&((r1_tarski(k1_relat_1(esk3_0),esk1_0)&r1_tarski(k2_relat_1(esk3_0),esk2_0))&~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.33/0.52  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,k2_zfmisc_1(X4,X3))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_10, c_0_16])).
% 0.33/0.52  cnf(c_0_21, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.33/0.52  cnf(c_0_22, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.33/0.52  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.33/0.52  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.33/0.52  cnf(c_0_25, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.33/0.52  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.33/0.52  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])]), ['proof']).
% 0.33/0.52  # SZS output end CNFRefutation
% 0.33/0.52  # Proof object total steps             : 28
% 0.33/0.52  # Proof object clause steps            : 17
% 0.33/0.52  # Proof object formula steps           : 11
% 0.33/0.52  # Proof object conjectures             : 8
% 0.33/0.52  # Proof object clause conjectures      : 5
% 0.33/0.52  # Proof object formula conjectures     : 3
% 0.33/0.52  # Proof object initial clauses used    : 10
% 0.33/0.52  # Proof object initial formulas used   : 5
% 0.33/0.52  # Proof object generating inferences   : 7
% 0.33/0.52  # Proof object simplifying inferences  : 4
% 0.33/0.52  # Training examples: 0 positive, 0 negative
% 0.33/0.52  # Parsed axioms                        : 5
% 0.33/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.33/0.52  # Initial clauses                      : 10
% 0.33/0.52  # Removed in clause preprocessing      : 0
% 0.33/0.52  # Initial clauses in saturation        : 10
% 0.33/0.52  # Processed clauses                    : 538
% 0.33/0.52  # ...of these trivial                  : 0
% 0.33/0.52  # ...subsumed                          : 106
% 0.33/0.52  # ...remaining for further processing  : 432
% 0.33/0.52  # Other redundant clauses eliminated   : 0
% 0.33/0.52  # Clauses deleted for lack of memory   : 0
% 0.33/0.52  # Backward-subsumed                    : 19
% 0.33/0.52  # Backward-rewritten                   : 0
% 0.33/0.52  # Generated clauses                    : 3041
% 0.33/0.52  # ...of the previous two non-trivial   : 3037
% 0.33/0.52  # Contextual simplify-reflections      : 0
% 0.33/0.52  # Paramodulations                      : 3041
% 0.33/0.52  # Factorizations                       : 0
% 0.33/0.52  # Equation resolutions                 : 0
% 0.33/0.52  # Propositional unsat checks           : 0
% 0.33/0.52  #    Propositional check models        : 0
% 0.33/0.52  #    Propositional check unsatisfiable : 0
% 0.33/0.52  #    Propositional clauses             : 0
% 0.33/0.52  #    Propositional clauses after purity: 0
% 0.33/0.52  #    Propositional unsat core size     : 0
% 0.33/0.52  #    Propositional preprocessing time  : 0.000
% 0.33/0.52  #    Propositional encoding time       : 0.000
% 0.33/0.52  #    Propositional solver time         : 0.000
% 0.33/0.52  #    Success case prop preproc time    : 0.000
% 0.33/0.52  #    Success case prop encoding time   : 0.000
% 0.33/0.52  #    Success case prop solver time     : 0.000
% 0.33/0.52  # Current number of processed clauses  : 403
% 0.33/0.52  #    Positive orientable unit clauses  : 3
% 0.33/0.52  #    Positive unorientable unit clauses: 0
% 0.33/0.52  #    Negative unit clauses             : 6
% 0.33/0.52  #    Non-unit-clauses                  : 394
% 0.33/0.52  # Current number of unprocessed clauses: 2519
% 0.33/0.52  # ...number of literals in the above   : 11332
% 0.33/0.52  # Current number of archived formulas  : 0
% 0.33/0.52  # Current number of archived clauses   : 29
% 0.33/0.52  # Clause-clause subsumption calls (NU) : 35044
% 0.33/0.52  # Rec. Clause-clause subsumption calls : 20845
% 0.33/0.52  # Non-unit clause-clause subsumptions  : 101
% 0.33/0.52  # Unit Clause-clause subsumption calls : 731
% 0.33/0.52  # Rewrite failures with RHS unbound    : 0
% 0.33/0.52  # BW rewrite match attempts            : 0
% 0.33/0.52  # BW rewrite match successes           : 0
% 0.33/0.52  # Condensation attempts                : 0
% 0.33/0.52  # Condensation successes               : 0
% 0.33/0.52  # Termbank termtop insertions          : 55561
% 0.33/0.52  
% 0.33/0.52  # -------------------------------------------------
% 0.33/0.52  # User time                : 0.159 s
% 0.33/0.52  # System time              : 0.006 s
% 0.33/0.52  # Total time               : 0.165 s
% 0.33/0.52  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
