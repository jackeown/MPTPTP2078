%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  50 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 125 expanded)
%              Number of equality atoms :   47 (  76 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t1_zfmisc_1,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X6
        | X7 != k1_tarski(X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k1_tarski(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) != X10
        | X11 = k1_tarski(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) = X10
        | X11 = k1_tarski(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_xboole_0)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_11,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | r1_tarski(X16,X14)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r1_tarski(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | ~ r1_tarski(esk2_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_tarski(esk2_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_12,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_tarski(esk2_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(assume_negation,[status(cth)],[t1_zfmisc_1])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( esk2_2(k1_xboole_0,X1) = k1_xboole_0
    | X1 = k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(fof_simplification,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( esk2_2(k1_xboole_0,k2_tarski(X1,X1)) = k1_xboole_0
    | esk2_2(k1_xboole_0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X1,X1) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_9])).

cnf(c_0_23,plain,
    ( esk2_2(k1_xboole_0,k2_tarski(X1,X1)) = k1_xboole_0
    | k2_tarski(X1,X1) = k1_zfmisc_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k1_zfmisc_1(k1_xboole_0) != k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_9])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_27,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( esk2_2(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.20/0.37  # and selection function SelectDiffNegLit.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.37  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.37  fof(t1_zfmisc_1, conjecture, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.20/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.37  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.37  fof(c_0_7, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.37  cnf(c_0_8, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_9, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  fof(c_0_10, plain, ![X5]:(~r1_tarski(X5,k1_xboole_0)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.37  fof(c_0_11, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|r1_tarski(X16,X14)|X15!=k1_zfmisc_1(X14))&(~r1_tarski(X17,X14)|r2_hidden(X17,X15)|X15!=k1_zfmisc_1(X14)))&((~r2_hidden(esk2_2(X18,X19),X19)|~r1_tarski(esk2_2(X18,X19),X18)|X19=k1_zfmisc_1(X18))&(r2_hidden(esk2_2(X18,X19),X19)|r1_tarski(esk2_2(X18,X19),X18)|X19=k1_zfmisc_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.37  cnf(c_0_12, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.37  cnf(c_0_13, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_14, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_tarski(esk2_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_15, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(assume_negation,[status(cth)],[t1_zfmisc_1])).
% 0.20/0.37  cnf(c_0_16, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_17, plain, (esk2_2(k1_xboole_0,X1)=k1_xboole_0|X1=k1_zfmisc_1(k1_xboole_0)|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.37  fof(c_0_18, negated_conjecture, k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0), inference(fof_simplification,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_19, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_20, plain, (esk2_2(k1_xboole_0,k2_tarski(X1,X1))=k1_xboole_0|esk2_2(k1_xboole_0,k2_tarski(X1,X1))=X1|k2_tarski(X1,X1)=k1_zfmisc_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_19, c_0_9])).
% 0.20/0.37  cnf(c_0_23, plain, (esk2_2(k1_xboole_0,k2_tarski(X1,X1))=k1_xboole_0|k2_tarski(X1,X1)=k1_zfmisc_1(k1_xboole_0)|X1!=k1_xboole_0), inference(ef,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (k1_zfmisc_1(k1_xboole_0)!=k2_tarski(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_21, c_0_9])).
% 0.20/0.37  cnf(c_0_25, plain, (r2_hidden(X1,X2)|X2!=k2_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.20/0.37  fof(c_0_26, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.37  cnf(c_0_27, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r1_tarski(esk2_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_28, plain, (esk2_2(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_24])).
% 0.20/0.37  cnf(c_0_29, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_30, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.37  cnf(c_0_31, plain, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])]), c_0_24]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 32
% 0.20/0.37  # Proof object clause steps            : 19
% 0.20/0.37  # Proof object formula steps           : 13
% 0.20/0.37  # Proof object conjectures             : 5
% 0.20/0.37  # Proof object clause conjectures      : 2
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 8
% 0.20/0.37  # Proof object initial formulas used   : 6
% 0.20/0.37  # Proof object generating inferences   : 7
% 0.20/0.37  # Proof object simplifying inferences  : 9
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 6
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 12
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 11
% 0.20/0.37  # Processed clauses                    : 49
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 3
% 0.20/0.37  # ...remaining for further processing  : 46
% 0.20/0.37  # Other redundant clauses eliminated   : 17
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 171
% 0.20/0.37  # ...of the previous two non-trivial   : 136
% 0.20/0.37  # Contextual simplify-reflections      : 1
% 0.20/0.37  # Paramodulations                      : 137
% 0.20/0.37  # Factorizations                       : 6
% 0.20/0.37  # Equation resolutions                 : 28
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 34
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 29
% 0.20/0.37  # Current number of unprocessed clauses: 109
% 0.20/0.37  # ...number of literals in the above   : 629
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 12
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 79
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 24
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3361
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.031 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.035 s
% 0.20/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
