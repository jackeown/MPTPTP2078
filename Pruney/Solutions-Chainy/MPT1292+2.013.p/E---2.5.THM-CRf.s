%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 119 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
              & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_tops_2])).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ( ~ m1_setfam_1(X9,X8)
        | r1_tarski(X8,k3_tarski(X9)) )
      & ( ~ r1_tarski(X8,k3_tarski(X9))
        | m1_setfam_1(X9,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & m1_setfam_1(esk3_0,u1_struct_0(esk2_0))
    & esk3_0 = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_13,negated_conjecture,
    ( m1_setfam_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_16,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ m1_setfam_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:44:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.026 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t5_tops_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 0.19/0.36  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.19/0.36  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.19/0.36  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.36  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.19/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.36  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.36  fof(c_0_8, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t5_tops_2])).
% 0.19/0.36  fof(c_0_9, plain, ![X8, X9]:((~m1_setfam_1(X9,X8)|r1_tarski(X8,k3_tarski(X9)))&(~r1_tarski(X8,k3_tarski(X9))|m1_setfam_1(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.19/0.36  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(m1_setfam_1(esk3_0,u1_struct_0(esk2_0))&esk3_0=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.36  cnf(c_0_11, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_12, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.19/0.36  cnf(c_0_13, negated_conjecture, (m1_setfam_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_14, negated_conjecture, (esk3_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  fof(c_0_15, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.36  fof(c_0_16, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.19/0.36  fof(c_0_17, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.36  cnf(c_0_18, plain, (r1_tarski(X1,k1_xboole_0)|~m1_setfam_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.36  cnf(c_0_19, negated_conjecture, (m1_setfam_1(k1_xboole_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.36  fof(c_0_20, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.36  cnf(c_0_21, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.36  cnf(c_0_22, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.36  fof(c_0_23, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.36  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.36  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.36  cnf(c_0_27, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.36  cnf(c_0_28, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.36  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.19/0.36  cnf(c_0_30, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_31, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_22, c_0_27])).
% 0.19/0.36  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])]), c_0_32]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 34
% 0.19/0.36  # Proof object clause steps            : 18
% 0.19/0.36  # Proof object formula steps           : 16
% 0.19/0.36  # Proof object conjectures             : 11
% 0.19/0.36  # Proof object clause conjectures      : 8
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 11
% 0.19/0.36  # Proof object initial formulas used   : 8
% 0.19/0.36  # Proof object generating inferences   : 5
% 0.19/0.36  # Proof object simplifying inferences  : 8
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 8
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 15
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 15
% 0.19/0.36  # Processed clauses                    : 40
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 40
% 0.19/0.36  # Other redundant clauses eliminated   : 2
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 4
% 0.19/0.36  # Generated clauses                    : 20
% 0.19/0.36  # ...of the previous two non-trivial   : 15
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 18
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 2
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 20
% 0.19/0.36  #    Positive orientable unit clauses  : 10
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 9
% 0.19/0.36  # Current number of unprocessed clauses: 3
% 0.19/0.36  # ...number of literals in the above   : 6
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 18
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 8
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 8
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 1
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 3
% 0.19/0.36  # BW rewrite match successes           : 2
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 882
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.026 s
% 0.19/0.36  # System time              : 0.004 s
% 0.19/0.36  # Total time               : 0.030 s
% 0.19/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
