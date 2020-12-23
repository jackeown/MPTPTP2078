%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:43 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 232 expanded)
%              Number of clauses        :   29 ( 112 expanded)
%              Number of leaves         :    4 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 (1232 expanded)
%              Number of equality atoms :   23 ( 276 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_0,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k5_xboole_0(X2,X3))
      <=> ~ ( r2_hidden(X1,X2)
          <=> r2_hidden(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t1_xboole_0])).

fof(c_0_5,negated_conjecture,
    ( ( ~ r2_hidden(esk3_0,esk4_0)
      | r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk3_0,esk4_0)
      | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r2_hidden(esk3_0,esk4_0)
      | ~ r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) )
    & ( r2_hidden(esk3_0,esk4_0)
      | r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X23,X24] : k5_xboole_0(X23,X24) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X23)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k4_xboole_0(esk5_0,esk4_0))
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk5_0,esk4_0))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_33]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_34]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_36]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t1_xboole_0, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.14/0.38  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.14/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.14/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.14/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3))))), inference(assume_negation,[status(cth)],[t1_xboole_0])).
% 0.14/0.38  fof(c_0_5, negated_conjecture, (((~r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)))&(~r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))))&((~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0)))&(r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.14/0.38  fof(c_0_6, plain, ![X23, X24]:k5_xboole_0(X23,X24)=k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.14/0.38  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.14/0.38  cnf(c_0_9, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_10, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_16, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))|~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  cnf(c_0_19, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_22, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))), inference(rw,[status(thm)],[c_0_14, c_0_10])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k5_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_26, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))|~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_17, c_0_10])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (~r2_hidden(esk3_0,k4_xboole_0(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.38  cnf(c_0_29, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk3_0,k4_xboole_0(esk5_0,esk4_0))|~r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))), inference(rw,[status(thm)],[c_0_25, c_0_10])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),k4_xboole_0(esk5_0,esk4_0)))|r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(esk5_0,esk4_0))|r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_33]), c_0_28])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_34]), c_0_32])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(esk4_0,X1))|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_35])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_36]), c_0_32]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 38
% 0.14/0.38  # Proof object clause steps            : 29
% 0.14/0.38  # Proof object formula steps           : 9
% 0.14/0.38  # Proof object conjectures             : 19
% 0.14/0.38  # Proof object clause conjectures      : 16
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 7
% 0.14/0.38  # Proof object simplifying inferences  : 20
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 17
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 16
% 0.14/0.38  # Processed clauses                    : 51
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 4
% 0.14/0.38  # ...remaining for further processing  : 47
% 0.14/0.38  # Other redundant clauses eliminated   : 6
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 5
% 0.14/0.38  # Generated clauses                    : 79
% 0.14/0.38  # ...of the previous two non-trivial   : 67
% 0.14/0.38  # Contextual simplify-reflections      : 5
% 0.14/0.38  # Paramodulations                      : 64
% 0.14/0.38  # Factorizations                       : 8
% 0.14/0.38  # Equation resolutions                 : 6
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
% 0.14/0.38  # Current number of processed clauses  : 19
% 0.14/0.38  #    Positive orientable unit clauses  : 1
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 14
% 0.14/0.38  # Current number of unprocessed clauses: 46
% 0.14/0.38  # ...number of literals in the above   : 160
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 23
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 123
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 73
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.38  # Unit Clause-clause subsumption calls : 11
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2298
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.033 s
% 0.14/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
