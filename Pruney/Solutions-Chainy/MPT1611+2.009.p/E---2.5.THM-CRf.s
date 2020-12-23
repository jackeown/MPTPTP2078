%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:53 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 (  70 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t19_yellow_1,conjecture,(
    ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X17] :
      ( v1_xboole_0(X17)
      | ~ r2_hidden(k3_tarski(X17),X17)
      | k4_yellow_0(k2_yellow_1(X17)) = k3_tarski(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_10,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | r1_tarski(X10,X8)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r1_tarski(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | ~ r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t19_yellow_1])).

fof(c_0_13,plain,(
    ! [X18] : k3_yellow_1(X18) = k2_yellow_1(k9_setfam_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_14,plain,(
    ! [X16] : k9_setfam_1(X16) = k1_zfmisc_1(X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X15] : k3_tarski(k1_zfmisc_1(X15)) = X15 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,negated_conjecture,(
    k4_yellow_0(k3_yellow_1(esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_21,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k4_yellow_0(k3_yellow_1(esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(esk2_0))) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:38:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.14/0.40  # and selection function HSelectMinInfpos.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.039 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.14/0.40  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.14/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.40  fof(t19_yellow_1, conjecture, ![X1]:k4_yellow_0(k3_yellow_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 0.14/0.40  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.14/0.40  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.14/0.40  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.14/0.40  fof(c_0_8, plain, ![X17]:(v1_xboole_0(X17)|(~r2_hidden(k3_tarski(X17),X17)|k4_yellow_0(k2_yellow_1(X17))=k3_tarski(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.14/0.40  fof(c_0_9, plain, ![X6, X7]:(~r2_hidden(X6,X7)|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.14/0.40  fof(c_0_10, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|r1_tarski(X10,X8)|X9!=k1_zfmisc_1(X8))&(~r1_tarski(X11,X8)|r2_hidden(X11,X9)|X9!=k1_zfmisc_1(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|~r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12))&(r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.40  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:k4_yellow_0(k3_yellow_1(X1))=X1), inference(assume_negation,[status(cth)],[t19_yellow_1])).
% 0.14/0.40  fof(c_0_13, plain, ![X18]:k3_yellow_1(X18)=k2_yellow_1(k9_setfam_1(X18)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.14/0.40  fof(c_0_14, plain, ![X16]:k9_setfam_1(X16)=k1_zfmisc_1(X16), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.14/0.40  cnf(c_0_15, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.40  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.40  fof(c_0_17, plain, ![X15]:k3_tarski(k1_zfmisc_1(X15))=X15, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.14/0.40  cnf(c_0_18, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.40  cnf(c_0_19, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  fof(c_0_20, negated_conjecture, k4_yellow_0(k3_yellow_1(esk2_0))!=esk2_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.14/0.40  cnf(c_0_21, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_22, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_23, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.40  cnf(c_0_24, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_25, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_18])).
% 0.14/0.40  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_27, negated_conjecture, (k4_yellow_0(k3_yellow_1(esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_28, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.40  cnf(c_0_29, plain, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1)))=X1|~r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.40  cnf(c_0_30, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(esk2_0)))!=esk2_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.40  cnf(c_0_32, plain, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.14/0.40  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 34
% 0.14/0.40  # Proof object clause steps            : 17
% 0.14/0.40  # Proof object formula steps           : 17
% 0.14/0.40  # Proof object conjectures             : 6
% 0.14/0.40  # Proof object clause conjectures      : 3
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 8
% 0.14/0.40  # Proof object initial formulas used   : 8
% 0.14/0.40  # Proof object generating inferences   : 2
% 0.14/0.40  # Proof object simplifying inferences  : 9
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 8
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 13
% 0.14/0.40  # Removed in clause preprocessing      : 2
% 0.14/0.40  # Initial clauses in saturation        : 11
% 0.14/0.40  # Processed clauses                    : 25
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 0
% 0.14/0.40  # ...remaining for further processing  : 25
% 0.14/0.40  # Other redundant clauses eliminated   : 4
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 0
% 0.14/0.40  # Backward-rewritten                   : 2
% 0.14/0.40  # Generated clauses                    : 8
% 0.14/0.40  # ...of the previous two non-trivial   : 6
% 0.14/0.40  # Contextual simplify-reflections      : 1
% 0.14/0.40  # Paramodulations                      : 4
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 4
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 9
% 0.14/0.40  #    Positive orientable unit clauses  : 4
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 0
% 0.14/0.40  #    Non-unit-clauses                  : 5
% 0.14/0.40  # Current number of unprocessed clauses: 2
% 0.14/0.40  # ...number of literals in the above   : 6
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 14
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 3
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 3
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.40  # Unit Clause-clause subsumption calls : 1
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 3
% 0.14/0.40  # BW rewrite match successes           : 2
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 784
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.038 s
% 0.14/0.40  # System time              : 0.006 s
% 0.14/0.40  # Total time               : 0.045 s
% 0.14/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
