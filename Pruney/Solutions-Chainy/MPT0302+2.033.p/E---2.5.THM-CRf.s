%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:35 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 139 expanded)
%              Number of clauses        :   22 (  59 expanded)
%              Number of leaves         :    4 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 417 expanded)
%              Number of equality atoms :   24 ( 212 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

fof(c_0_5,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk2_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r2_hidden(X10,X12)
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) )
      & ( r2_hidden(X11,X13)
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) )
      & ( ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X11,X13)
        | r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_8,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk4_0)),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_9])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk3_0),esk2_1(esk4_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk3_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14]),c_0_25])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.21/0.47  # and selection function SelectSmallestOrientable.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.038 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 0.21/0.47  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.47  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.21/0.47  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.21/0.47  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 0.21/0.47  fof(c_0_5, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk3_0!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.21/0.47  fof(c_0_6, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk2_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.47  fof(c_0_7, plain, ![X10, X11, X12, X13]:(((r2_hidden(X10,X12)|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)))&(r2_hidden(X11,X13)|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13))))&(~r2_hidden(X10,X12)|~r2_hidden(X11,X13)|r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.21/0.47  cnf(c_0_8, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.47  cnf(c_0_9, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.47  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.47  cnf(c_0_11, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.21/0.47  cnf(c_0_12, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.47  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.47  cnf(c_0_14, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.47  cnf(c_0_15, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk4_0)),k2_zfmisc_1(X2,esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.21/0.47  cnf(c_0_16, negated_conjecture, (r2_hidden(esk2_1(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_9])).
% 0.21/0.47  fof(c_0_17, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.21/0.47  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.47  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk3_0),esk2_1(esk4_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.47  cnf(c_0_20, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.47  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.47  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_1(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.47  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_16])).
% 0.21/0.47  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)|r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21])])).
% 0.21/0.47  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_22])).
% 0.21/0.47  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk2_1(esk3_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_14]), c_0_25])).
% 0.21/0.47  cnf(c_0_27, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.47  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_26])).
% 0.21/0.47  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_26])).
% 0.21/0.47  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_20]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 31
% 0.21/0.47  # Proof object clause steps            : 22
% 0.21/0.47  # Proof object formula steps           : 9
% 0.21/0.47  # Proof object conjectures             : 20
% 0.21/0.47  # Proof object clause conjectures      : 17
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 9
% 0.21/0.47  # Proof object initial formulas used   : 4
% 0.21/0.47  # Proof object generating inferences   : 13
% 0.21/0.47  # Proof object simplifying inferences  : 6
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 4
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 10
% 0.21/0.47  # Removed in clause preprocessing      : 0
% 0.21/0.47  # Initial clauses in saturation        : 10
% 0.21/0.47  # Processed clauses                    : 158
% 0.21/0.47  # ...of these trivial                  : 2
% 0.21/0.47  # ...subsumed                          : 37
% 0.21/0.47  # ...remaining for further processing  : 119
% 0.21/0.47  # Other redundant clauses eliminated   : 12
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 0
% 0.21/0.47  # Backward-rewritten                   : 3
% 0.21/0.47  # Generated clauses                    : 4998
% 0.21/0.47  # ...of the previous two non-trivial   : 4098
% 0.21/0.47  # Contextual simplify-reflections      : 1
% 0.21/0.47  # Paramodulations                      : 4982
% 0.21/0.47  # Factorizations                       : 4
% 0.21/0.47  # Equation resolutions                 : 12
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 106
% 0.21/0.47  #    Positive orientable unit clauses  : 20
% 0.21/0.47  #    Positive unorientable unit clauses: 0
% 0.21/0.47  #    Negative unit clauses             : 3
% 0.21/0.47  #    Non-unit-clauses                  : 83
% 0.21/0.47  # Current number of unprocessed clauses: 3938
% 0.21/0.47  # ...number of literals in the above   : 13275
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 13
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 531
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 422
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 37
% 0.21/0.47  # Unit Clause-clause subsumption calls : 16
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 20
% 0.21/0.47  # BW rewrite match successes           : 1
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 81831
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.119 s
% 0.21/0.47  # System time              : 0.009 s
% 0.21/0.47  # Total time               : 0.128 s
% 0.21/0.47  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
