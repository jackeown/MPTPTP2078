%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:54 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  63 expanded)
%              Number of equality atoms :   31 (  34 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t19_yellow_1,conjecture,(
    ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_10,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X7)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r1_tarski(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | ~ r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X5,X6] : r1_tarski(k3_xboole_0(X5,X6),X5) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_12,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t19_yellow_1])).

fof(c_0_14,plain,(
    ! [X21] : k3_yellow_1(X21) = k2_yellow_1(k9_setfam_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_15,plain,(
    ! [X18] : k9_setfam_1(X18) = k1_zfmisc_1(X18) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_16,plain,(
    ! [X19] : k3_yellow_1(X19) = k3_lattice3(k1_lattice3(X19)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,(
    k4_yellow_0(k3_yellow_1(esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_21,plain,(
    ! [X20] :
      ( v1_xboole_0(X20)
      | ~ r2_hidden(k3_tarski(X20),X20)
      | k4_yellow_0(k2_yellow_1(X20)) = k3_tarski(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_22,plain,(
    ! [X16] : k3_tarski(k1_zfmisc_1(X16)) = X16 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_23,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_28,plain,(
    ! [X17] : ~ v1_xboole_0(k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_29,negated_conjecture,
    ( k4_yellow_0(k3_yellow_1(esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_yellow_1(k1_zfmisc_1(X1)) = k3_lattice3(k1_lattice3(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k4_yellow_0(k3_lattice3(k1_lattice3(esk2_0))) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_36,plain,
    ( k4_yellow_0(k3_lattice3(k1_lattice3(X1))) = X1 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S083N
% 0.14/0.37  # and selection function SelectCQArNT.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.37  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.14/0.37  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.14/0.37  fof(t19_yellow_1, conjecture, ![X1]:k4_yellow_0(k3_yellow_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 0.14/0.37  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.14/0.37  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.14/0.37  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.14/0.37  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.14/0.37  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.14/0.37  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.14/0.37  fof(c_0_10, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|r1_tarski(X9,X7)|X8!=k1_zfmisc_1(X7))&(~r1_tarski(X10,X7)|r2_hidden(X10,X8)|X8!=k1_zfmisc_1(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|~r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11))&(r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.37  fof(c_0_11, plain, ![X5, X6]:r1_tarski(k3_xboole_0(X5,X6),X5), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.14/0.37  fof(c_0_12, plain, ![X4]:k3_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.14/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:k4_yellow_0(k3_yellow_1(X1))=X1), inference(assume_negation,[status(cth)],[t19_yellow_1])).
% 0.14/0.37  fof(c_0_14, plain, ![X21]:k3_yellow_1(X21)=k2_yellow_1(k9_setfam_1(X21)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.14/0.37  fof(c_0_15, plain, ![X18]:k9_setfam_1(X18)=k1_zfmisc_1(X18), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.14/0.37  fof(c_0_16, plain, ![X19]:k3_yellow_1(X19)=k3_lattice3(k1_lattice3(X19)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.14/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_18, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_19, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  fof(c_0_20, negated_conjecture, k4_yellow_0(k3_yellow_1(esk2_0))!=esk2_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.37  fof(c_0_21, plain, ![X20]:(v1_xboole_0(X20)|(~r2_hidden(k3_tarski(X20),X20)|k4_yellow_0(k2_yellow_1(X20))=k3_tarski(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.14/0.37  fof(c_0_22, plain, ![X16]:k3_tarski(k1_zfmisc_1(X16))=X16, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.14/0.37  cnf(c_0_23, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_24, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_25, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  cnf(c_0_26, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.37  fof(c_0_28, plain, ![X17]:~v1_xboole_0(k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (k4_yellow_0(k3_yellow_1(esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_30, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  cnf(c_0_31, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.37  cnf(c_0_32, plain, (k2_yellow_1(k1_zfmisc_1(X1))=k3_lattice3(k1_lattice3(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.14/0.37  cnf(c_0_33, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.37  cnf(c_0_34, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (k4_yellow_0(k3_lattice3(k1_lattice3(esk2_0)))!=esk2_0), inference(rw,[status(thm)],[c_0_29, c_0_25])).
% 0.14/0.37  cnf(c_0_36, plain, (k4_yellow_0(k3_lattice3(k1_lattice3(X1)))=X1), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 38
% 0.14/0.37  # Proof object clause steps            : 17
% 0.14/0.37  # Proof object formula steps           : 21
% 0.14/0.37  # Proof object conjectures             : 6
% 0.14/0.37  # Proof object clause conjectures      : 3
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 10
% 0.14/0.37  # Proof object initial formulas used   : 10
% 0.14/0.37  # Proof object generating inferences   : 3
% 0.14/0.37  # Proof object simplifying inferences  : 10
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 11
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 14
% 0.14/0.37  # Removed in clause preprocessing      : 2
% 0.14/0.37  # Initial clauses in saturation        : 12
% 0.14/0.37  # Processed clauses                    : 29
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 29
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 1
% 0.14/0.37  # Generated clauses                    : 9
% 0.14/0.37  # ...of the previous two non-trivial   : 6
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 7
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
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
% 0.14/0.37  # Current number of processed clauses  : 14
% 0.14/0.37  #    Positive orientable unit clauses  : 8
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 5
% 0.14/0.37  # Current number of unprocessed clauses: 1
% 0.14/0.37  # ...number of literals in the above   : 3
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 15
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 2
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 4
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 851
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.026 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.030 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
