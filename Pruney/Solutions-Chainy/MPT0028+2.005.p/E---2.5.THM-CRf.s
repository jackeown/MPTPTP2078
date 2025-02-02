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
% DateTime   : Thu Dec  3 10:31:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  50 expanded)
%              Number of clauses        :   18 (  27 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 304 expanded)
%              Number of equality atoms :   32 (  97 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t21_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(c_0_3,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_4,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(assume_negation,[status(cth)],[t21_xboole_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_11]),c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X2)
    | r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_18,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,(
    k3_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_18,c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.20/0.46  # and selection function SelectVGNonCR.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.027 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.46  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.46  fof(t21_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.46  fof(c_0_3, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15))&(r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|~r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k3_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|~r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k3_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))&(r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.46  cnf(c_0_4, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.46  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.46  cnf(c_0_6, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.46  cnf(c_0_7, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.46  cnf(c_0_8, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.46  cnf(c_0_9, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_4])).
% 0.20/0.46  cnf(c_0_10, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.46  cnf(c_0_11, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_6])).
% 0.20/0.46  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_7])).
% 0.20/0.46  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.20/0.46  cnf(c_0_14, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_10])).
% 0.20/0.46  fof(c_0_15, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(assume_negation,[status(cth)],[t21_xboole_1])).
% 0.20/0.46  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_11]), c_0_11])).
% 0.20/0.46  cnf(c_0_17, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,X2)|r2_hidden(esk2_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_12, c_0_11])).
% 0.20/0.46  cnf(c_0_18, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk2_3(k2_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.46  fof(c_0_19, negated_conjecture, k3_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0))!=esk3_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.46  cnf(c_0_20, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.46  cnf(c_0_21, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_18, c_0_9])).
% 0.20/0.46  cnf(c_0_22, negated_conjecture, (k3_xboole_0(esk3_0,k2_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_23, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.46  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 25
% 0.20/0.46  # Proof object clause steps            : 18
% 0.20/0.46  # Proof object formula steps           : 7
% 0.20/0.46  # Proof object conjectures             : 5
% 0.20/0.46  # Proof object clause conjectures      : 2
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 6
% 0.20/0.46  # Proof object initial formulas used   : 3
% 0.20/0.46  # Proof object generating inferences   : 11
% 0.20/0.46  # Proof object simplifying inferences  : 4
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 3
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 13
% 0.20/0.46  # Removed in clause preprocessing      : 0
% 0.20/0.46  # Initial clauses in saturation        : 13
% 0.20/0.46  # Processed clauses                    : 515
% 0.20/0.46  # ...of these trivial                  : 102
% 0.20/0.46  # ...subsumed                          : 251
% 0.20/0.46  # ...remaining for further processing  : 162
% 0.20/0.46  # Other redundant clauses eliminated   : 107
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 0
% 0.20/0.46  # Backward-rewritten                   : 2
% 0.20/0.46  # Generated clauses                    : 8847
% 0.20/0.46  # ...of the previous two non-trivial   : 6618
% 0.20/0.46  # Contextual simplify-reflections      : 3
% 0.20/0.46  # Paramodulations                      : 8589
% 0.20/0.46  # Factorizations                       : 140
% 0.20/0.46  # Equation resolutions                 : 118
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 147
% 0.20/0.46  #    Positive orientable unit clauses  : 53
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 0
% 0.20/0.46  #    Non-unit-clauses                  : 94
% 0.20/0.46  # Current number of unprocessed clauses: 6128
% 0.20/0.46  # ...number of literals in the above   : 16631
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 15
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 2695
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 1847
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 254
% 0.20/0.46  # Unit Clause-clause subsumption calls : 197
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 156
% 0.20/0.46  # BW rewrite match successes           : 2
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 92369
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.104 s
% 0.20/0.46  # System time              : 0.010 s
% 0.20/0.46  # Total time               : 0.114 s
% 0.20/0.46  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
