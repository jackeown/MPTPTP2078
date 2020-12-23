%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:52 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 (  96 expanded)
%              Number of equality atoms :   42 (  42 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
          & r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t55_zfmisc_1])).

fof(c_0_6,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)
    & r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k4_xboole_0(X15,X16) = X15 )
      & ( k4_xboole_0(X15,X16) != X15
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X21,X20)
        | X21 = X17
        | X21 = X18
        | X21 = X19
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X17
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X18
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( X22 != X19
        | r2_hidden(X22,X20)
        | X20 != k1_enumset1(X17,X18,X19) )
      & ( esk2_4(X23,X24,X25,X26) != X23
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( esk2_4(X23,X24,X25,X26) != X24
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( esk2_4(X23,X24,X25,X26) != X25
        | ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | esk2_4(X23,X24,X25,X26) = X23
        | esk2_4(X23,X24,X25,X26) = X24
        | esk2_4(X23,X24,X25,X26) = X25
        | X26 = k1_enumset1(X23,X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0) = k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:47:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t55_zfmisc_1, conjecture, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.37  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3)))), inference(assume_negation,[status(cth)],[t55_zfmisc_1])).
% 0.12/0.37  fof(c_0_6, negated_conjecture, (r1_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)&r2_hidden(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_8, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X15, X16]:((~r1_xboole_0(X15,X16)|k4_xboole_0(X15,X16)=X15)&(k4_xboole_0(X15,X16)!=X15|r1_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (r1_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_11, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (r1_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  fof(c_0_15, plain, ![X17, X18, X19, X20, X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X21,X20)|(X21=X17|X21=X18|X21=X19)|X20!=k1_enumset1(X17,X18,X19))&(((X22!=X17|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19))&(X22!=X18|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19)))&(X22!=X19|r2_hidden(X22,X20)|X20!=k1_enumset1(X17,X18,X19))))&((((esk2_4(X23,X24,X25,X26)!=X23|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25))&(esk2_4(X23,X24,X25,X26)!=X24|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25)))&(esk2_4(X23,X24,X25,X26)!=X25|~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_enumset1(X23,X24,X25)))&(r2_hidden(esk2_4(X23,X24,X25,X26),X26)|(esk2_4(X23,X24,X25,X26)=X23|esk2_4(X23,X24,X25,X26)=X24|esk2_4(X23,X24,X25,X26)=X25)|X26=k1_enumset1(X23,X24,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.12/0.37  cnf(c_0_16, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (k4_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_20, plain, (r2_hidden(X1,k1_enumset1(X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 23
% 0.12/0.37  # Proof object clause steps            : 12
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 9
% 0.12/0.37  # Proof object clause conjectures      : 6
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 6
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 3
% 0.12/0.37  # Proof object simplifying inferences  : 6
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 19
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 18
% 0.12/0.37  # Processed clauses                    : 36
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 36
% 0.12/0.37  # Other redundant clauses eliminated   : 10
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 14
% 0.12/0.37  # ...of the previous two non-trivial   : 9
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 7
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 10
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 11
% 0.12/0.37  #    Positive orientable unit clauses  : 6
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 5
% 0.12/0.37  # Current number of unprocessed clauses: 9
% 0.12/0.37  # ...number of literals in the above   : 31
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 19
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 28
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 15
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 6
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1269
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.022 s
% 0.12/0.37  # System time              : 0.009 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
