%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  56 expanded)
%              Number of clauses        :   15 (  24 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 109 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_setfam_1,conjecture,(
    ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t80_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(assume_negation,[status(cth)],[t61_setfam_1])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,X15)
      | X15 = k1_xboole_0
      | m1_subset_1(k1_tarski(X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

fof(c_0_10,plain,(
    ! [X14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_11,negated_conjecture,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X13] : r1_tarski(k1_tarski(X13),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t80_zfmisc_1])).

cnf(c_0_15,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_zfmisc_1(X1) = k1_xboole_0
    | m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(X5,esk1_3(X5,X6,X7))
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X7,X6)
        | X6 = k2_xboole_0(X5,X7) )
      & ( r1_tarski(X7,esk1_3(X5,X6,X7))
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X7,X6)
        | X6 = k2_xboole_0(X5,X7) )
      & ( ~ r1_tarski(X6,esk1_3(X5,X6,X7))
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X7,X6)
        | X6 = k2_xboole_0(X5,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X11,X12] : k2_xboole_0(k1_tarski(X11),X12) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,esk1_3(k1_tarski(esk2_0),k1_xboole_0,X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_26]),c_0_29]),c_0_23])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:52:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.044 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t61_setfam_1, conjecture, ![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 0.20/0.38  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 0.20/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.38  fof(t80_zfmisc_1, axiom, ![X1]:r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 0.20/0.38  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.20/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.20/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(assume_negation,[status(cth)],[t61_setfam_1])).
% 0.20/0.38  fof(c_0_9, plain, ![X15, X16]:(~m1_subset_1(X16,X15)|(X15=k1_xboole_0|m1_subset_1(k1_tarski(X16),k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 0.20/0.38  fof(c_0_10, plain, ![X14]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.38  cnf(c_0_12, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_13, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_14, plain, ![X13]:r1_tarski(k1_tarski(X13),k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t80_zfmisc_1])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_16, plain, (k1_zfmisc_1(X1)=k1_xboole_0|m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  fof(c_0_17, plain, ![X5, X6, X7]:(((r1_tarski(X5,esk1_3(X5,X6,X7))|(~r1_tarski(X5,X6)|~r1_tarski(X7,X6))|X6=k2_xboole_0(X5,X7))&(r1_tarski(X7,esk1_3(X5,X6,X7))|(~r1_tarski(X5,X6)|~r1_tarski(X7,X6))|X6=k2_xboole_0(X5,X7)))&(~r1_tarski(X6,esk1_3(X5,X6,X7))|(~r1_tarski(X5,X6)|~r1_tarski(X7,X6))|X6=k2_xboole_0(X5,X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.20/0.38  cnf(c_0_18, plain, (r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (k1_zfmisc_1(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  fof(c_0_20, plain, ![X11, X12]:k2_xboole_0(k1_tarski(X11),X12)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.20/0.38  fof(c_0_21, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_24, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_25, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_26, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_27, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(X1,esk1_3(k1_tarski(esk2_0),k1_xboole_0,X1))|~r1_tarski(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.20/0.38  cnf(c_0_29, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_30, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_26])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_26]), c_0_29]), c_0_23])]), c_0_30]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 32
% 0.20/0.38  # Proof object clause steps            : 15
% 0.20/0.38  # Proof object formula steps           : 17
% 0.20/0.38  # Proof object conjectures             : 8
% 0.20/0.38  # Proof object clause conjectures      : 5
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 9
% 0.20/0.38  # Proof object initial formulas used   : 8
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 6
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 9
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 11
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 11
% 0.20/0.38  # Processed clauses                    : 31
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 31
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 19
% 0.20/0.38  # ...of the previous two non-trivial   : 19
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 19
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 19
% 0.20/0.38  #    Positive orientable unit clauses  : 7
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 9
% 0.20/0.38  # Current number of unprocessed clauses: 8
% 0.20/0.38  # ...number of literals in the above   : 24
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 12
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 9
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 5
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1041
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.045 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.050 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
