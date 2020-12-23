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
% DateTime   : Thu Dec  3 10:50:24 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   31 (  61 expanded)
%              Number of clauses        :   15 (  30 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 130 expanded)
%              Number of equality atoms :   32 (  71 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(t129_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(t126_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k2_relat_1(X1),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(t138_relat_1,conjecture,(
    ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_9,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X10,X11,X14,X16,X17] :
      ( ( ~ v1_relat_1(X10)
        | ~ r2_hidden(X11,X10)
        | X11 = k4_tarski(esk1_2(X10,X11),esk2_2(X10,X11)) )
      & ( r2_hidden(esk3_1(X14),X14)
        | v1_relat_1(X14) )
      & ( esk3_1(X14) != k4_tarski(X16,X17)
        | v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(X19,X20)
      | k8_relat_1(X20,k8_relat_1(X19,X21)) = k8_relat_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_relat_1])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k8_relat_1(k2_relat_1(X18),X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t138_relat_1])).

cnf(c_0_19,plain,
    ( k8_relat_1(X3,k8_relat_1(X2,X1)) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_22,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_24,negated_conjecture,(
    k8_relat_1(esk4_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_25,plain,
    ( k8_relat_1(X1,k8_relat_1(X2,k1_xboole_0)) = k8_relat_1(X2,k1_xboole_0)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k8_relat_1(esk4_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:17:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.18/0.35  # and selection function SelectSmallestOrientable.
% 0.18/0.35  #
% 0.18/0.35  # Preprocessing time       : 0.016 s
% 0.18/0.35  # Presaturation interreduction done
% 0.18/0.35  
% 0.18/0.35  # Proof found!
% 0.18/0.35  # SZS status Theorem
% 0.18/0.35  # SZS output start CNFRefutation
% 0.18/0.35  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.35  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.35  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.18/0.35  fof(t129_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 0.18/0.35  fof(t126_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k2_relat_1(X1),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 0.18/0.35  fof(t138_relat_1, conjecture, ![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 0.18/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.35  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.18/0.35  fof(c_0_8, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.35  fof(c_0_9, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.35  cnf(c_0_10, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.35  cnf(c_0_11, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.35  cnf(c_0_12, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_10])).
% 0.18/0.35  fof(c_0_13, plain, ![X10, X11, X14, X16, X17]:((~v1_relat_1(X10)|(~r2_hidden(X11,X10)|X11=k4_tarski(esk1_2(X10,X11),esk2_2(X10,X11))))&((r2_hidden(esk3_1(X14),X14)|v1_relat_1(X14))&(esk3_1(X14)!=k4_tarski(X16,X17)|v1_relat_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.18/0.35  fof(c_0_14, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(X19,X20)|k8_relat_1(X20,k8_relat_1(X19,X21))=k8_relat_1(X19,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_relat_1])])).
% 0.18/0.35  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.18/0.35  cnf(c_0_16, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.35  fof(c_0_17, plain, ![X18]:(~v1_relat_1(X18)|k8_relat_1(k2_relat_1(X18),X18)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).
% 0.18/0.35  fof(c_0_18, negated_conjecture, ~(![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t138_relat_1])).
% 0.18/0.35  cnf(c_0_19, plain, (k8_relat_1(X3,k8_relat_1(X2,X1))=k8_relat_1(X2,X1)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.35  cnf(c_0_20, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.35  fof(c_0_21, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.35  cnf(c_0_22, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.35  cnf(c_0_23, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.18/0.35  fof(c_0_24, negated_conjecture, k8_relat_1(esk4_0,k1_xboole_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.18/0.35  cnf(c_0_25, plain, (k8_relat_1(X1,k8_relat_1(X2,k1_xboole_0))=k8_relat_1(X2,k1_xboole_0)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.35  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.35  cnf(c_0_27, plain, (k8_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_23])).
% 0.18/0.35  cnf(c_0_28, negated_conjecture, (k8_relat_1(esk4_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.35  cnf(c_0_29, plain, (k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_27])).
% 0.18/0.35  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])]), ['proof']).
% 0.18/0.35  # SZS output end CNFRefutation
% 0.18/0.35  # Proof object total steps             : 31
% 0.18/0.35  # Proof object clause steps            : 15
% 0.18/0.35  # Proof object formula steps           : 16
% 0.18/0.35  # Proof object conjectures             : 5
% 0.18/0.35  # Proof object clause conjectures      : 2
% 0.18/0.35  # Proof object formula conjectures     : 3
% 0.18/0.35  # Proof object initial clauses used    : 8
% 0.18/0.35  # Proof object initial formulas used   : 8
% 0.18/0.35  # Proof object generating inferences   : 5
% 0.18/0.35  # Proof object simplifying inferences  : 6
% 0.18/0.35  # Training examples: 0 positive, 0 negative
% 0.18/0.35  # Parsed axioms                        : 8
% 0.18/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.35  # Initial clauses                      : 13
% 0.18/0.35  # Removed in clause preprocessing      : 0
% 0.18/0.35  # Initial clauses in saturation        : 13
% 0.18/0.35  # Processed clauses                    : 33
% 0.18/0.35  # ...of these trivial                  : 0
% 0.18/0.35  # ...subsumed                          : 0
% 0.18/0.35  # ...remaining for further processing  : 33
% 0.18/0.35  # Other redundant clauses eliminated   : 2
% 0.18/0.35  # Clauses deleted for lack of memory   : 0
% 0.18/0.35  # Backward-subsumed                    : 0
% 0.18/0.35  # Backward-rewritten                   : 3
% 0.18/0.35  # Generated clauses                    : 8
% 0.18/0.35  # ...of the previous two non-trivial   : 8
% 0.18/0.35  # Contextual simplify-reflections      : 0
% 0.18/0.35  # Paramodulations                      : 6
% 0.18/0.35  # Factorizations                       : 0
% 0.18/0.35  # Equation resolutions                 : 2
% 0.18/0.35  # Propositional unsat checks           : 0
% 0.18/0.35  #    Propositional check models        : 0
% 0.18/0.35  #    Propositional check unsatisfiable : 0
% 0.18/0.35  #    Propositional clauses             : 0
% 0.18/0.35  #    Propositional clauses after purity: 0
% 0.18/0.35  #    Propositional unsat core size     : 0
% 0.18/0.35  #    Propositional preprocessing time  : 0.000
% 0.18/0.35  #    Propositional encoding time       : 0.000
% 0.18/0.35  #    Propositional solver time         : 0.000
% 0.18/0.35  #    Success case prop preproc time    : 0.000
% 0.18/0.35  #    Success case prop encoding time   : 0.000
% 0.18/0.35  #    Success case prop solver time     : 0.000
% 0.18/0.35  # Current number of processed clauses  : 15
% 0.18/0.35  #    Positive orientable unit clauses  : 7
% 0.18/0.35  #    Positive unorientable unit clauses: 0
% 0.18/0.35  #    Negative unit clauses             : 3
% 0.18/0.35  #    Non-unit-clauses                  : 5
% 0.18/0.35  # Current number of unprocessed clauses: 1
% 0.18/0.35  # ...number of literals in the above   : 3
% 0.18/0.35  # Current number of archived formulas  : 0
% 0.18/0.35  # Current number of archived clauses   : 16
% 0.18/0.35  # Clause-clause subsumption calls (NU) : 5
% 0.18/0.35  # Rec. Clause-clause subsumption calls : 5
% 0.18/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.35  # Unit Clause-clause subsumption calls : 1
% 0.18/0.35  # Rewrite failures with RHS unbound    : 0
% 0.18/0.35  # BW rewrite match attempts            : 3
% 0.18/0.35  # BW rewrite match successes           : 3
% 0.18/0.35  # Condensation attempts                : 0
% 0.18/0.35  # Condensation successes               : 0
% 0.18/0.35  # Termbank termtop insertions          : 775
% 0.18/0.35  
% 0.18/0.35  # -------------------------------------------------
% 0.18/0.35  # User time                : 0.017 s
% 0.18/0.35  # System time              : 0.003 s
% 0.18/0.35  # Total time               : 0.020 s
% 0.18/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
