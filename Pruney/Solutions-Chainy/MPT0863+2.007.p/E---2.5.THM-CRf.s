%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:17 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   25 (  96 expanded)
%              Number of clauses        :   18 (  43 expanded)
%              Number of leaves         :    3 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 448 expanded)
%              Number of equality atoms :   54 ( 314 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & ( k2_mcart_1(X1) = X4
          | k2_mcart_1(X1) = X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & ( k2_mcart_1(X1) = X4
            | k2_mcart_1(X1) = X5 ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_mcart_1])).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_5,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(k1_mcart_1(X15),X16)
        | ~ r2_hidden(X15,k2_zfmisc_1(X16,X17)) )
      & ( r2_hidden(k2_mcart_1(X15),X17)
        | ~ r2_hidden(X15,k2_zfmisc_1(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))
    & ( k2_mcart_1(esk2_0) != esk5_0
      | k1_mcart_1(esk2_0) != esk3_0 )
    & ( k2_mcart_1(esk2_0) != esk6_0
      | k1_mcart_1(esk2_0) != esk3_0 )
    & ( k2_mcart_1(esk2_0) != esk5_0
      | k1_mcart_1(esk2_0) != esk4_0 )
    & ( k2_mcart_1(esk2_0) != esk6_0
      | k1_mcart_1(esk2_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_7,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk6_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk5_0
    | k2_mcart_1(esk2_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0
    | k1_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk6_0
    | k1_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk4_0 ),
    inference(sr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0
    | k1_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_15,c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:25:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.11/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.026 s
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t19_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&(k2_mcart_1(X1)=X4|k2_mcart_1(X1)=X5))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 0.11/0.36  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.11/0.36  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.11/0.36  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&(k2_mcart_1(X1)=X4|k2_mcart_1(X1)=X5)))), inference(assume_negation,[status(cth)],[t19_mcart_1])).
% 0.11/0.36  fof(c_0_4, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.11/0.36  fof(c_0_5, plain, ![X15, X16, X17]:((r2_hidden(k1_mcart_1(X15),X16)|~r2_hidden(X15,k2_zfmisc_1(X16,X17)))&(r2_hidden(k2_mcart_1(X15),X17)|~r2_hidden(X15,k2_zfmisc_1(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.11/0.36  fof(c_0_6, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))&(((k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0)&(k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk3_0))&((k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk4_0)&(k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.11/0.36  cnf(c_0_7, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.11/0.36  cnf(c_0_8, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.11/0.36  cnf(c_0_9, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_10, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.11/0.36  cnf(c_0_11, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_7])).
% 0.11/0.36  cnf(c_0_12, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_tarski(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.11/0.36  cnf(c_0_13, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_tarski(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_10, c_0_9])).
% 0.11/0.36  cnf(c_0_14, negated_conjecture, (k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_15, negated_conjecture, (k2_mcart_1(esk2_0)=esk5_0|k2_mcart_1(esk2_0)=esk6_0), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.11/0.36  cnf(c_0_16, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_17, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0|k1_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_11, c_0_13])).
% 0.11/0.36  cnf(c_0_18, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.11/0.36  cnf(c_0_19, negated_conjecture, (k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_20, negated_conjecture, (k1_mcart_1(esk2_0)=esk4_0), inference(sr,[status(thm)],[c_0_17, c_0_18])).
% 0.11/0.36  cnf(c_0_21, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_22, negated_conjecture, (k2_mcart_1(esk2_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.11/0.36  cnf(c_0_23, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_20])])).
% 0.11/0.36  cnf(c_0_24, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_15, c_0_22]), c_0_23]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 25
% 0.11/0.36  # Proof object clause steps            : 18
% 0.11/0.36  # Proof object formula steps           : 7
% 0.11/0.36  # Proof object conjectures             : 17
% 0.11/0.36  # Proof object clause conjectures      : 14
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 8
% 0.11/0.36  # Proof object initial formulas used   : 3
% 0.11/0.36  # Proof object generating inferences   : 5
% 0.11/0.36  # Proof object simplifying inferences  : 9
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 3
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 13
% 0.11/0.36  # Removed in clause preprocessing      : 0
% 0.11/0.36  # Initial clauses in saturation        : 13
% 0.11/0.36  # Processed clauses                    : 30
% 0.11/0.36  # ...of these trivial                  : 0
% 0.11/0.36  # ...subsumed                          : 2
% 0.11/0.36  # ...remaining for further processing  : 27
% 0.11/0.36  # Other redundant clauses eliminated   : 5
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 6
% 0.11/0.36  # Generated clauses                    : 27
% 0.11/0.36  # ...of the previous two non-trivial   : 27
% 0.11/0.36  # Contextual simplify-reflections      : 1
% 0.11/0.36  # Paramodulations                      : 20
% 0.11/0.36  # Factorizations                       : 2
% 0.11/0.36  # Equation resolutions                 : 5
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 16
% 0.11/0.36  #    Positive orientable unit clauses  : 5
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 4
% 0.11/0.36  #    Non-unit-clauses                  : 7
% 0.11/0.36  # Current number of unprocessed clauses: 10
% 0.11/0.36  # ...number of literals in the above   : 24
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 8
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 15
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 11
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.11/0.36  # Unit Clause-clause subsumption calls : 12
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 6
% 0.11/0.36  # BW rewrite match successes           : 1
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 861
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.025 s
% 0.11/0.36  # System time              : 0.005 s
% 0.11/0.36  # Total time               : 0.031 s
% 0.11/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
