%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:19 EST 2020

% Result     : Timeout 58.31s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   33 ( 115 expanded)
%              Number of clauses        :   18 (  51 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 250 expanded)
%              Number of equality atoms :   33 ( 133 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t48_xboole_1])).

fof(c_0_8,plain,(
    ! [X36,X37] : k4_xboole_0(k2_xboole_0(X36,X37),X37) = k4_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_9,plain,(
    ! [X34,X35] : k2_xboole_0(X34,k4_xboole_0(X35,X34)) = k2_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_10,negated_conjecture,(
    k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) != k3_xboole_0(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k3_xboole_0(X38,X39)) = k4_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_15,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_16,plain,(
    ! [X30,X31] : k2_xboole_0(X30,k3_xboole_0(X30,X31)) = X30 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_17,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) != k3_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))
    | r2_hidden(esk1_3(X1,X2,k3_xboole_0(esk4_0,esk5_0)),X1)
    | k4_xboole_0(X1,X2) != k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_3(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2),k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))
    | r2_hidden(esk1_3(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2),k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(X1,X2))
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_3(k3_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k3_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0)),k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_25]),c_0_29])]),c_0_17]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 58.31/58.53  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 58.31/58.53  # and selection function SelectNegativeLiterals.
% 58.31/58.53  #
% 58.31/58.53  # Preprocessing time       : 0.027 s
% 58.31/58.53  # Presaturation interreduction done
% 58.31/58.53  
% 58.31/58.53  # Proof found!
% 58.31/58.53  # SZS status Theorem
% 58.31/58.53  # SZS output start CNFRefutation
% 58.31/58.53  fof(t48_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 58.31/58.53  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 58.31/58.53  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 58.31/58.53  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 58.31/58.53  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 58.31/58.53  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 58.31/58.53  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 58.31/58.53  fof(c_0_7, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t48_xboole_1])).
% 58.31/58.53  fof(c_0_8, plain, ![X36, X37]:k4_xboole_0(k2_xboole_0(X36,X37),X37)=k4_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 58.31/58.53  fof(c_0_9, plain, ![X34, X35]:k2_xboole_0(X34,k4_xboole_0(X35,X34))=k2_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 58.31/58.53  fof(c_0_10, negated_conjecture, k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))!=k3_xboole_0(esk4_0,esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 58.31/58.53  fof(c_0_11, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 58.31/58.53  cnf(c_0_12, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 58.31/58.53  cnf(c_0_13, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 58.31/58.53  fof(c_0_14, plain, ![X38, X39]:k4_xboole_0(X38,k3_xboole_0(X38,X39))=k4_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 58.31/58.53  fof(c_0_15, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 58.31/58.53  fof(c_0_16, plain, ![X30, X31]:k2_xboole_0(X30,k3_xboole_0(X30,X31))=X30, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 58.31/58.53  cnf(c_0_17, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))!=k3_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 58.31/58.53  cnf(c_0_18, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 58.31/58.53  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 58.31/58.53  cnf(c_0_20, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.31/58.53  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 58.31/58.53  cnf(c_0_22, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 58.31/58.53  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 58.31/58.53  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))|r2_hidden(esk1_3(X1,X2,k3_xboole_0(esk4_0,esk5_0)),X1)|k4_xboole_0(X1,X2)!=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 58.31/58.53  cnf(c_0_25, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 58.31/58.53  cnf(c_0_26, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_23])).
% 58.31/58.53  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_3(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2),k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))|r2_hidden(esk1_3(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2),k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(X1,X2))|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 58.31/58.53  cnf(c_0_28, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 58.31/58.53  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_3(k3_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))), inference(er,[status(thm)],[c_0_27])).
% 58.31/58.53  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 58.31/58.53  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk1_3(k3_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0)),k4_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 58.31/58.53  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_25]), c_0_29])]), c_0_17]), c_0_31]), ['proof']).
% 58.31/58.53  # SZS output end CNFRefutation
% 58.31/58.53  # Proof object total steps             : 33
% 58.31/58.53  # Proof object clause steps            : 18
% 58.31/58.53  # Proof object formula steps           : 15
% 58.31/58.53  # Proof object conjectures             : 9
% 58.31/58.53  # Proof object clause conjectures      : 6
% 58.31/58.53  # Proof object formula conjectures     : 3
% 58.31/58.53  # Proof object initial clauses used    : 9
% 58.31/58.53  # Proof object initial formulas used   : 7
% 58.31/58.53  # Proof object generating inferences   : 8
% 58.31/58.53  # Proof object simplifying inferences  : 8
% 58.31/58.53  # Training examples: 0 positive, 0 negative
% 58.31/58.53  # Parsed axioms                        : 11
% 58.31/58.53  # Removed by relevancy pruning/SinE    : 0
% 58.31/58.53  # Initial clauses                      : 20
% 58.31/58.53  # Removed in clause preprocessing      : 0
% 58.31/58.53  # Initial clauses in saturation        : 20
% 58.31/58.53  # Processed clauses                    : 29705
% 58.31/58.53  # ...of these trivial                  : 4116
% 58.31/58.53  # ...subsumed                          : 20346
% 58.31/58.53  # ...remaining for further processing  : 5242
% 58.31/58.53  # Other redundant clauses eliminated   : 37274
% 58.31/58.53  # Clauses deleted for lack of memory   : 261345
% 58.31/58.53  # Backward-subsumed                    : 96
% 58.31/58.53  # Backward-rewritten                   : 236
% 58.31/58.53  # Generated clauses                    : 6413799
% 58.31/58.53  # ...of the previous two non-trivial   : 5551420
% 58.31/58.53  # Contextual simplify-reflections      : 70
% 58.31/58.53  # Paramodulations                      : 6376097
% 58.31/58.53  # Factorizations                       : 400
% 58.31/58.53  # Equation resolutions                 : 37302
% 58.31/58.53  # Propositional unsat checks           : 0
% 58.31/58.53  #    Propositional check models        : 0
% 58.31/58.53  #    Propositional check unsatisfiable : 0
% 58.31/58.53  #    Propositional clauses             : 0
% 58.31/58.53  #    Propositional clauses after purity: 0
% 58.31/58.53  #    Propositional unsat core size     : 0
% 58.31/58.53  #    Propositional preprocessing time  : 0.000
% 58.31/58.53  #    Propositional encoding time       : 0.000
% 58.31/58.53  #    Propositional solver time         : 0.000
% 58.31/58.53  #    Success case prop preproc time    : 0.000
% 58.31/58.53  #    Success case prop encoding time   : 0.000
% 58.31/58.53  #    Success case prop solver time     : 0.000
% 58.31/58.53  # Current number of processed clauses  : 4887
% 58.31/58.53  #    Positive orientable unit clauses  : 666
% 58.31/58.53  #    Positive unorientable unit clauses: 1
% 58.31/58.53  #    Negative unit clauses             : 264
% 58.31/58.53  #    Non-unit-clauses                  : 3956
% 58.31/58.53  # Current number of unprocessed clauses: 1988415
% 58.31/58.53  # ...number of literals in the above   : 8202773
% 58.31/58.53  # Current number of archived formulas  : 0
% 58.31/58.53  # Current number of archived clauses   : 352
% 58.31/58.53  # Clause-clause subsumption calls (NU) : 2318598
% 58.31/58.53  # Rec. Clause-clause subsumption calls : 1321850
% 58.31/58.53  # Non-unit clause-clause subsumptions  : 16838
% 58.31/58.53  # Unit Clause-clause subsumption calls : 86528
% 58.31/58.53  # Rewrite failures with RHS unbound    : 0
% 58.31/58.53  # BW rewrite match attempts            : 2664
% 58.31/58.53  # BW rewrite match successes           : 101
% 58.31/58.53  # Condensation attempts                : 0
% 58.31/58.53  # Condensation successes               : 0
% 58.31/58.53  # Termbank termtop insertions          : 148648173
% 58.37/58.60  
% 58.37/58.60  # -------------------------------------------------
% 58.37/58.60  # User time                : 57.149 s
% 58.37/58.60  # System time              : 1.074 s
% 58.37/58.60  # Total time               : 58.223 s
% 58.37/58.60  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
