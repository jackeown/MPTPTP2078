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
% DateTime   : Thu Dec  3 11:08:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 144 expanded)
%              Number of clauses        :   19 (  63 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 448 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,X2)
        & v1_finset_1(X2) )
     => v1_finset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(fc17_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(t25_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
    <=> v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(l22_finset_1,axiom,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
     => v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(c_0_6,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | ~ v1_finset_1(X10)
      | v1_finset_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).

fof(c_0_7,plain,(
    ! [X3] : r1_tarski(X3,k1_zfmisc_1(k3_tarski(X3))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_8,plain,
    ( v1_finset_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X6] :
      ( ~ v1_finset_1(X6)
      | v1_finset_1(k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_finset_1(X1)
          & ! [X2] :
              ( r2_hidden(X2,X1)
             => v1_finset_1(X2) ) )
      <=> v1_finset_1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t25_finset_1])).

cnf(c_0_12,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( v1_finset_1(k1_zfmisc_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ! [X13] :
      ( ( r2_hidden(esk3_0,esk2_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ v1_finset_1(esk3_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( v1_finset_1(esk2_0)
        | v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ r2_hidden(X13,esk2_0)
        | v1_finset_1(X13)
        | v1_finset_1(k3_tarski(esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | r1_tarski(X4,k3_tarski(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

cnf(c_0_16,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_finset_1(esk2_0)
    | v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_finset_1(esk3_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X7] :
      ( ( r2_hidden(esk1_1(X7),X7)
        | ~ v1_finset_1(X7)
        | v1_finset_1(k3_tarski(X7)) )
      & ( ~ v1_finset_1(esk1_1(X7))
        | ~ v1_finset_1(X7)
        | v1_finset_1(k3_tarski(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).

cnf(c_0_23,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk2_0))
    | ~ v1_finset_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( v1_finset_1(X1)
    | v1_finset_1(k3_tarski(esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(esk1_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_finset_1(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20])]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.039 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t13_finset_1, axiom, ![X1, X2]:((r1_tarski(X1,X2)&v1_finset_1(X2))=>v1_finset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_finset_1)).
% 0.14/0.39  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.14/0.39  fof(fc17_finset_1, axiom, ![X1]:(v1_finset_1(X1)=>v1_finset_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_finset_1)).
% 0.14/0.39  fof(t25_finset_1, conjecture, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_finset_1)).
% 0.14/0.39  fof(t92_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 0.14/0.39  fof(l22_finset_1, axiom, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_finset_1)).
% 0.14/0.39  fof(c_0_6, plain, ![X9, X10]:(~r1_tarski(X9,X10)|~v1_finset_1(X10)|v1_finset_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).
% 0.14/0.39  fof(c_0_7, plain, ![X3]:r1_tarski(X3,k1_zfmisc_1(k3_tarski(X3))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.14/0.39  cnf(c_0_8, plain, (v1_finset_1(X1)|~r1_tarski(X1,X2)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_9, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  fof(c_0_10, plain, ![X6]:(~v1_finset_1(X6)|v1_finset_1(k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).
% 0.14/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t25_finset_1])).
% 0.14/0.39  cnf(c_0_12, plain, (v1_finset_1(X1)|~v1_finset_1(k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.39  cnf(c_0_13, plain, (v1_finset_1(k1_zfmisc_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  fof(c_0_14, negated_conjecture, ![X13]:(((r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0)))&(~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))))&((v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0)))&(~r2_hidden(X13,esk2_0)|v1_finset_1(X13)|v1_finset_1(k3_tarski(esk2_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).
% 0.14/0.39  fof(c_0_15, plain, ![X4, X5]:(~r2_hidden(X4,X5)|r1_tarski(X4,k3_tarski(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).
% 0.14/0.39  cnf(c_0_16, plain, (v1_finset_1(X1)|~v1_finset_1(k3_tarski(X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.39  cnf(c_0_17, negated_conjecture, (v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (v1_finset_1(esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  fof(c_0_22, plain, ![X7]:((r2_hidden(esk1_1(X7),X7)|~v1_finset_1(X7)|v1_finset_1(k3_tarski(X7)))&(~v1_finset_1(esk1_1(X7))|~v1_finset_1(X7)|v1_finset_1(k3_tarski(X7)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).
% 0.14/0.39  cnf(c_0_23, plain, (v1_finset_1(X1)|~v1_finset_1(k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_8, c_0_18])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (~v1_finset_1(k3_tarski(esk2_0))|~v1_finset_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_20])])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (v1_finset_1(X1)|v1_finset_1(k3_tarski(esk2_0))|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_27, plain, (r2_hidden(esk1_1(X1),X1)|v1_finset_1(k3_tarski(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (~v1_finset_1(k3_tarski(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.14/0.39  cnf(c_0_29, plain, (v1_finset_1(k3_tarski(X1))|~v1_finset_1(esk1_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (v1_finset_1(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_20])]), c_0_28])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_20])]), c_0_28]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 32
% 0.14/0.39  # Proof object clause steps            : 19
% 0.14/0.39  # Proof object formula steps           : 13
% 0.14/0.39  # Proof object conjectures             : 13
% 0.14/0.39  # Proof object clause conjectures      : 10
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 10
% 0.14/0.39  # Proof object initial formulas used   : 6
% 0.14/0.39  # Proof object generating inferences   : 7
% 0.14/0.39  # Proof object simplifying inferences  : 11
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 6
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 10
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 10
% 0.14/0.39  # Processed clauses                    : 18
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 18
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 3
% 0.14/0.39  # Generated clauses                    : 11
% 0.14/0.39  # ...of the previous two non-trivial   : 9
% 0.14/0.39  # Contextual simplify-reflections      : 1
% 0.14/0.39  # Paramodulations                      : 11
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 15
% 0.14/0.39  #    Positive orientable unit clauses  : 3
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 1
% 0.14/0.39  #    Non-unit-clauses                  : 11
% 0.14/0.39  # Current number of unprocessed clauses: 0
% 0.14/0.39  # ...number of literals in the above   : 0
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 3
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 15
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 14
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.39  # Unit Clause-clause subsumption calls : 3
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 1
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 843
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.037 s
% 0.14/0.39  # System time              : 0.007 s
% 0.14/0.39  # Total time               : 0.044 s
% 0.14/0.39  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
