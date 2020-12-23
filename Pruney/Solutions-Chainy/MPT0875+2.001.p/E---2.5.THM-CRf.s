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
% DateTime   : Thu Dec  3 10:59:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 107 expanded)
%              Number of clauses        :   18 (  48 expanded)
%              Number of leaves         :    3 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 352 expanded)
%              Number of equality atoms :   66 ( 351 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 )
      <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t35_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( ( esk1_0 = k1_xboole_0
      | esk2_0 = k1_xboole_0
      | esk3_0 = k1_xboole_0
      | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0 )
    & ( esk1_0 != k1_xboole_0
      | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 )
    & ( esk2_0 != k1_xboole_0
      | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 )
    & ( esk3_0 != k1_xboole_0
      | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] : k3_zfmisc_1(X6,X7,X8) = k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X4,X5] :
      ( ( k2_zfmisc_1(X4,X5) != k1_xboole_0
        | X4 = k1_xboole_0
        | X5 = k1_xboole_0 )
      & ( X4 != k1_xboole_0
        | k2_zfmisc_1(X4,X5) = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X4,X5) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_7,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_9,c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_10])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_16]),c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_21]),c_0_21]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:46:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.029 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t35_mcart_1, conjecture, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.19/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.37  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0)), inference(assume_negation,[status(cth)],[t35_mcart_1])).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ((esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k1_xboole_0)&(((esk1_0!=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0)&(esk2_0!=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0))&(esk3_0!=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.19/0.37  fof(c_0_5, plain, ![X6, X7, X8]:k3_zfmisc_1(X6,X7,X8)=k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.37  fof(c_0_6, plain, ![X4, X5]:((k2_zfmisc_1(X4,X5)!=k1_xboole_0|(X4=k1_xboole_0|X5=k1_xboole_0))&((X4!=k1_xboole_0|k2_zfmisc_1(X4,X5)=k1_xboole_0)&(X5!=k1_xboole_0|k2_zfmisc_1(X4,X5)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_7, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_8, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_9, negated_conjecture, (esk3_0!=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_10, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.37  cnf(c_0_12, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (esk2_0!=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (esk3_0!=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_9, c_0_8])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_10])).
% 0.19/0.37  cnf(c_0_16, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (esk1_0!=k1_xboole_0|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (esk2_0!=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_13, c_0_8])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.19/0.37  cnf(c_0_21, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (esk1_0!=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_8])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_16]), c_0_21])])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_21]), c_0_21]), c_0_23])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 25
% 0.19/0.37  # Proof object clause steps            : 18
% 0.19/0.37  # Proof object formula steps           : 7
% 0.19/0.37  # Proof object conjectures             : 15
% 0.19/0.37  # Proof object clause conjectures      : 12
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 8
% 0.19/0.37  # Proof object initial formulas used   : 3
% 0.19/0.37  # Proof object generating inferences   : 3
% 0.19/0.37  # Proof object simplifying inferences  : 17
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 3
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 8
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 7
% 0.19/0.37  # Processed clauses                    : 19
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 19
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 2
% 0.19/0.37  # Backward-rewritten                   : 4
% 0.19/0.37  # Generated clauses                    : 12
% 0.19/0.37  # ...of the previous two non-trivial   : 8
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 10
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 4
% 0.19/0.37  #    Positive orientable unit clauses  : 3
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 0
% 0.19/0.37  #    Non-unit-clauses                  : 1
% 0.19/0.37  # Current number of unprocessed clauses: 1
% 0.19/0.37  # ...number of literals in the above   : 2
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 14
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.37  # Unit Clause-clause subsumption calls : 2
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 544
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
