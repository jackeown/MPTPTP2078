%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:53 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   25 (  47 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 226 expanded)
%              Number of equality atoms :   14 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | v1_partfun1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t132_funct_2])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ( v1_funct_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | v1_xboole_0(X10) )
      & ( v1_partfun1(X11,X9)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ~ v1_partfun1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | X4 = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_9,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_partfun1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_xboole_0(X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_partfun1(X8,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk2_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_19,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_10]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.31  % Computer   : n014.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % WCLimit    : 600
% 0.13/0.31  % DateTime   : Tue Dec  1 12:38:52 EST 2020
% 0.13/0.31  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.34  #
% 0.17/0.34  # Preprocessing time       : 0.027 s
% 0.17/0.34  # Presaturation interreduction done
% 0.17/0.34  
% 0.17/0.34  # Proof found!
% 0.17/0.34  # SZS status Theorem
% 0.17/0.34  # SZS output start CNFRefutation
% 0.17/0.34  fof(t132_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 0.17/0.34  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.17/0.34  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.17/0.34  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.17/0.34  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.17/0.34  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1))))), inference(assume_negation,[status(cth)],[t132_funct_2])).
% 0.17/0.34  fof(c_0_6, plain, ![X9, X10, X11]:((v1_funct_1(X11)|(~v1_funct_1(X11)|~v1_funct_2(X11,X9,X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_xboole_0(X10))&(v1_partfun1(X11,X9)|(~v1_funct_1(X11)|~v1_funct_2(X11,X9,X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_xboole_0(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.17/0.34  fof(c_0_7, negated_conjecture, ((v1_funct_1(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&~v1_partfun1(esk3_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.17/0.34  fof(c_0_8, plain, ![X4, X5]:(~v1_xboole_0(X4)|X4=X5|~v1_xboole_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.17/0.34  cnf(c_0_9, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.34  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.34  cnf(c_0_11, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.34  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.34  cnf(c_0_13, negated_conjecture, (~v1_partfun1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.34  cnf(c_0_14, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.34  cnf(c_0_15, negated_conjecture, (v1_xboole_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.17/0.34  fof(c_0_16, plain, ![X6, X7, X8]:(~v1_xboole_0(X6)|(~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))|v1_partfun1(X8,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.17/0.34  cnf(c_0_17, negated_conjecture, (X1=esk2_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.34  cnf(c_0_18, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.17/0.34  cnf(c_0_19, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.34  cnf(c_0_20, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.34  cnf(c_0_21, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.17/0.34  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_10]), c_0_13])).
% 0.17/0.34  cnf(c_0_23, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.17/0.34  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_18])]), ['proof']).
% 0.17/0.34  # SZS output end CNFRefutation
% 0.17/0.34  # Proof object total steps             : 25
% 0.17/0.34  # Proof object clause steps            : 15
% 0.17/0.34  # Proof object formula steps           : 10
% 0.17/0.34  # Proof object conjectures             : 14
% 0.17/0.34  # Proof object clause conjectures      : 11
% 0.17/0.34  # Proof object formula conjectures     : 3
% 0.17/0.34  # Proof object initial clauses used    : 9
% 0.17/0.34  # Proof object initial formulas used   : 5
% 0.17/0.34  # Proof object generating inferences   : 4
% 0.17/0.34  # Proof object simplifying inferences  : 10
% 0.17/0.34  # Training examples: 0 positive, 0 negative
% 0.17/0.34  # Parsed axioms                        : 5
% 0.17/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.34  # Initial clauses                      : 12
% 0.17/0.34  # Removed in clause preprocessing      : 1
% 0.17/0.34  # Initial clauses in saturation        : 11
% 0.17/0.34  # Processed clauses                    : 25
% 0.17/0.34  # ...of these trivial                  : 2
% 0.17/0.34  # ...subsumed                          : 0
% 0.17/0.34  # ...remaining for further processing  : 23
% 0.17/0.34  # Other redundant clauses eliminated   : 0
% 0.17/0.34  # Clauses deleted for lack of memory   : 0
% 0.17/0.34  # Backward-subsumed                    : 0
% 0.17/0.34  # Backward-rewritten                   : 7
% 0.17/0.34  # Generated clauses                    : 5
% 0.17/0.34  # ...of the previous two non-trivial   : 9
% 0.17/0.34  # Contextual simplify-reflections      : 0
% 0.17/0.34  # Paramodulations                      : 5
% 0.17/0.34  # Factorizations                       : 0
% 0.17/0.34  # Equation resolutions                 : 0
% 0.17/0.34  # Propositional unsat checks           : 0
% 0.17/0.34  #    Propositional check models        : 0
% 0.17/0.34  #    Propositional check unsatisfiable : 0
% 0.17/0.34  #    Propositional clauses             : 0
% 0.17/0.34  #    Propositional clauses after purity: 0
% 0.17/0.34  #    Propositional unsat core size     : 0
% 0.17/0.34  #    Propositional preprocessing time  : 0.000
% 0.17/0.34  #    Propositional encoding time       : 0.000
% 0.17/0.34  #    Propositional solver time         : 0.000
% 0.17/0.34  #    Success case prop preproc time    : 0.000
% 0.17/0.34  #    Success case prop encoding time   : 0.000
% 0.17/0.34  #    Success case prop solver time     : 0.000
% 0.17/0.34  # Current number of processed clauses  : 7
% 0.17/0.34  #    Positive orientable unit clauses  : 4
% 0.17/0.34  #    Positive unorientable unit clauses: 0
% 0.17/0.34  #    Negative unit clauses             : 0
% 0.17/0.34  #    Non-unit-clauses                  : 3
% 0.17/0.34  # Current number of unprocessed clauses: 4
% 0.17/0.34  # ...number of literals in the above   : 6
% 0.17/0.34  # Current number of archived formulas  : 0
% 0.17/0.34  # Current number of archived clauses   : 16
% 0.17/0.34  # Clause-clause subsumption calls (NU) : 8
% 0.17/0.34  # Rec. Clause-clause subsumption calls : 2
% 0.17/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.17/0.34  # Unit Clause-clause subsumption calls : 2
% 0.17/0.34  # Rewrite failures with RHS unbound    : 0
% 0.17/0.34  # BW rewrite match attempts            : 2
% 0.17/0.34  # BW rewrite match successes           : 2
% 0.17/0.34  # Condensation attempts                : 0
% 0.17/0.34  # Condensation successes               : 0
% 0.17/0.34  # Termbank termtop insertions          : 809
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.027 s
% 0.17/0.35  # System time              : 0.004 s
% 0.17/0.35  # Total time               : 0.031 s
% 0.17/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
