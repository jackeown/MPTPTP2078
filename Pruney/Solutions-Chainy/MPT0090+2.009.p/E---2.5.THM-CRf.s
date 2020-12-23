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
% DateTime   : Thu Dec  3 10:33:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  90 expanded)
%              Number of clauses        :   16 (  39 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 217 expanded)
%              Number of equality atoms :   24 (  88 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(X1,X2)
      <=> k4_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t83_xboole_1])).

fof(c_0_7,plain,(
    ! [X39,X40] : r1_xboole_0(k4_xboole_0(X39,X40),X40) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_8,negated_conjecture,
    ( ( ~ r1_xboole_0(esk3_0,esk4_0)
      | k4_xboole_0(esk3_0,esk4_0) != esk3_0 )
    & ( r1_xboole_0(esk3_0,esk4_0)
      | k4_xboole_0(esk3_0,esk4_0) = esk3_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k3_xboole_0(X30,X31)) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_10,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_11,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_16,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r1_xboole_0(X16,X17)
        | r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X21,k3_xboole_0(X19,X20))
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0)
    | k4_xboole_0(esk3_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_23,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1),X2)
    | r2_hidden(esk1_3(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk3_0),esk3_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19]),c_0_26])]),c_0_22]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:16:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.46  # and selection function SelectNegativeLiterals.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.026 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t83_xboole_1, conjecture, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.46  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.46  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.46  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.46  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.46  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.46  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1)), inference(assume_negation,[status(cth)],[t83_xboole_1])).
% 0.19/0.46  fof(c_0_7, plain, ![X39, X40]:r1_xboole_0(k4_xboole_0(X39,X40),X40), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.46  fof(c_0_8, negated_conjecture, ((~r1_xboole_0(esk3_0,esk4_0)|k4_xboole_0(esk3_0,esk4_0)!=esk3_0)&(r1_xboole_0(esk3_0,esk4_0)|k4_xboole_0(esk3_0,esk4_0)=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.46  fof(c_0_9, plain, ![X30, X31]:k4_xboole_0(X30,k3_xboole_0(X30,X31))=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.46  fof(c_0_10, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.46  cnf(c_0_11, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.46  cnf(c_0_12, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)|k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_13, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.46  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  fof(c_0_15, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.46  fof(c_0_16, plain, ![X16, X17, X19, X20, X21]:((r1_xboole_0(X16,X17)|r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)))&(~r2_hidden(X21,k3_xboole_0(X19,X20))|~r1_xboole_0(X19,X20))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.46  cnf(c_0_17, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)|k4_xboole_0(esk3_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_18, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.46  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.46  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_21, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.46  cnf(c_0_22, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18])])).
% 0.19/0.46  cnf(c_0_23, plain, (X1=k4_xboole_0(X2,X3)|r2_hidden(esk1_3(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1),X2)|r2_hidden(esk1_3(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.46  cnf(c_0_24, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_21, c_0_14])).
% 0.19/0.46  cnf(c_0_25, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk3_0),esk3_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23])])).
% 0.19/0.46  cnf(c_0_27, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.19/0.46  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_19]), c_0_26])]), c_0_22]), c_0_27]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 29
% 0.19/0.46  # Proof object clause steps            : 16
% 0.19/0.46  # Proof object formula steps           : 13
% 0.19/0.46  # Proof object conjectures             : 10
% 0.19/0.46  # Proof object clause conjectures      : 7
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 8
% 0.19/0.46  # Proof object initial formulas used   : 6
% 0.19/0.46  # Proof object generating inferences   : 5
% 0.19/0.46  # Proof object simplifying inferences  : 10
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 13
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 20
% 0.19/0.46  # Removed in clause preprocessing      : 1
% 0.19/0.46  # Initial clauses in saturation        : 19
% 0.19/0.46  # Processed clauses                    : 708
% 0.19/0.46  # ...of these trivial                  : 45
% 0.19/0.46  # ...subsumed                          : 468
% 0.19/0.46  # ...remaining for further processing  : 195
% 0.19/0.46  # Other redundant clauses eliminated   : 94
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 2
% 0.19/0.46  # Backward-rewritten                   : 35
% 0.19/0.46  # Generated clauses                    : 7739
% 0.19/0.46  # ...of the previous two non-trivial   : 6028
% 0.19/0.46  # Contextual simplify-reflections      : 0
% 0.19/0.46  # Paramodulations                      : 7643
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 96
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 136
% 0.19/0.46  #    Positive orientable unit clauses  : 67
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 14
% 0.19/0.46  #    Non-unit-clauses                  : 55
% 0.19/0.46  # Current number of unprocessed clauses: 5214
% 0.19/0.46  # ...number of literals in the above   : 13801
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 57
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 667
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 616
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 149
% 0.19/0.46  # Unit Clause-clause subsumption calls : 85
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 206
% 0.19/0.46  # BW rewrite match successes           : 26
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 100808
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.108 s
% 0.19/0.46  # System time              : 0.013 s
% 0.19/0.46  # Total time               : 0.121 s
% 0.19/0.46  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
