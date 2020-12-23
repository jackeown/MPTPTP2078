%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(fc17_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_finset_1)).

fof(t25_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
    <=> v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_finset_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(l22_finset_1,axiom,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
     => v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_finset_1)).

fof(c_0_6,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | ~ v1_finset_1(X10)
      | v1_finset_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).

fof(c_0_7,plain,(
    ! [X5] : r1_tarski(X5,k1_zfmisc_1(k3_tarski(X5))) ),
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
    ! [X3,X4] :
      ( ~ r2_hidden(X3,X4)
      | r1_tarski(X3,k3_tarski(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:28:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t13_finset_1, axiom, ![X1, X2]:((r1_tarski(X1,X2)&v1_finset_1(X2))=>v1_finset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 0.14/0.38  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.14/0.38  fof(fc17_finset_1, axiom, ![X1]:(v1_finset_1(X1)=>v1_finset_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_finset_1)).
% 0.14/0.38  fof(t25_finset_1, conjecture, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_finset_1)).
% 0.14/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.14/0.38  fof(l22_finset_1, axiom, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_finset_1)).
% 0.14/0.38  fof(c_0_6, plain, ![X9, X10]:(~r1_tarski(X9,X10)|~v1_finset_1(X10)|v1_finset_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).
% 0.14/0.38  fof(c_0_7, plain, ![X5]:r1_tarski(X5,k1_zfmisc_1(k3_tarski(X5))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.14/0.38  cnf(c_0_8, plain, (v1_finset_1(X1)|~r1_tarski(X1,X2)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_9, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_10, plain, ![X6]:(~v1_finset_1(X6)|v1_finset_1(k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).
% 0.14/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t25_finset_1])).
% 0.14/0.38  cnf(c_0_12, plain, (v1_finset_1(X1)|~v1_finset_1(k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.38  cnf(c_0_13, plain, (v1_finset_1(k1_zfmisc_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_14, negated_conjecture, ![X13]:(((r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0)))&(~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))))&((v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0)))&(~r2_hidden(X13,esk2_0)|v1_finset_1(X13)|v1_finset_1(k3_tarski(esk2_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).
% 0.14/0.38  fof(c_0_15, plain, ![X3, X4]:(~r2_hidden(X3,X4)|r1_tarski(X3,k3_tarski(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.14/0.38  cnf(c_0_16, plain, (v1_finset_1(X1)|~v1_finset_1(k3_tarski(X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (v1_finset_1(esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_22, plain, ![X7]:((r2_hidden(esk1_1(X7),X7)|~v1_finset_1(X7)|v1_finset_1(k3_tarski(X7)))&(~v1_finset_1(esk1_1(X7))|~v1_finset_1(X7)|v1_finset_1(k3_tarski(X7)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).
% 0.14/0.38  cnf(c_0_23, plain, (v1_finset_1(X1)|~v1_finset_1(k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_8, c_0_18])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (~v1_finset_1(k3_tarski(esk2_0))|~v1_finset_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_20])])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (v1_finset_1(X1)|v1_finset_1(k3_tarski(esk2_0))|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_27, plain, (r2_hidden(esk1_1(X1),X1)|v1_finset_1(k3_tarski(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (~v1_finset_1(k3_tarski(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.14/0.38  cnf(c_0_29, plain, (v1_finset_1(k3_tarski(X1))|~v1_finset_1(esk1_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (v1_finset_1(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_20])]), c_0_28])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_20])]), c_0_28]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 32
% 0.14/0.38  # Proof object clause steps            : 19
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 13
% 0.14/0.38  # Proof object clause conjectures      : 10
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 10
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 7
% 0.14/0.38  # Proof object simplifying inferences  : 11
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 10
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 10
% 0.14/0.38  # Processed clauses                    : 18
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 18
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 3
% 0.14/0.38  # Generated clauses                    : 11
% 0.14/0.38  # ...of the previous two non-trivial   : 9
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 11
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 15
% 0.14/0.38  #    Positive orientable unit clauses  : 3
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 11
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 3
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 16
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 14
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 3
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 843
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.024 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.030 s
% 0.14/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
