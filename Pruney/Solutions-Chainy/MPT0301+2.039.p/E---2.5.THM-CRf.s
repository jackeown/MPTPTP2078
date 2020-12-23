%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:30 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 461 expanded)
%              Number of clauses        :   26 ( 244 expanded)
%              Number of leaves         :    5 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 (2518 expanded)
%              Number of equality atoms :   55 ( 918 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r2_hidden(X7,X8)
        | ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( r2_hidden(X7,X8)
        | r2_hidden(X7,X9)
        | ~ r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X7,X8)
        | r2_hidden(X7,X9)
        | r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X7,X9)
        | r2_hidden(X7,X8)
        | r2_hidden(X7,k5_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_6,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16,X19,X20,X21,X22,X23,X24,X26,X27] :
      ( ( r2_hidden(esk2_4(X13,X14,X15,X16),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( r2_hidden(esk3_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( X16 = k4_tarski(esk2_4(X13,X14,X15,X16),esk3_4(X13,X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( ~ r2_hidden(X20,X13)
        | ~ r2_hidden(X21,X14)
        | X19 != k4_tarski(X20,X21)
        | r2_hidden(X19,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X24),X24)
        | ~ r2_hidden(X26,X22)
        | ~ r2_hidden(X27,X23)
        | esk4_3(X22,X23,X24) != k4_tarski(X26,X27)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk5_3(X22,X23,X24),X22)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk6_3(X22,X23,X24),X23)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( esk4_3(X22,X23,X24) = k4_tarski(esk5_3(X22,X23,X24),esk6_3(X22,X23,X24))
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(esk3_4(X1,k1_xboole_0,k2_zfmisc_1(X1,k1_xboole_0),X2),X3)
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_14,plain,(
    ! [X10] :
      ( X10 = k1_xboole_0
      | r2_hidden(esk1_1(X10),X10) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_19,negated_conjecture,
    ( ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
      | esk7_0 = k1_xboole_0
      | esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_3(X2,k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_20])])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:30:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.21/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.38  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.21/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.38  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.38  fof(c_0_5, plain, ![X7, X8, X9]:(((~r2_hidden(X7,X8)|~r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9)))&(r2_hidden(X7,X8)|r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9))))&((~r2_hidden(X7,X8)|r2_hidden(X7,X9)|r2_hidden(X7,k5_xboole_0(X8,X9)))&(~r2_hidden(X7,X9)|r2_hidden(X7,X8)|r2_hidden(X7,k5_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.21/0.38  fof(c_0_6, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.38  fof(c_0_7, plain, ![X13, X14, X15, X16, X19, X20, X21, X22, X23, X24, X26, X27]:(((((r2_hidden(esk2_4(X13,X14,X15,X16),X13)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14))&(r2_hidden(esk3_4(X13,X14,X15,X16),X14)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(X16=k4_tarski(esk2_4(X13,X14,X15,X16),esk3_4(X13,X14,X15,X16))|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(~r2_hidden(X20,X13)|~r2_hidden(X21,X14)|X19!=k4_tarski(X20,X21)|r2_hidden(X19,X15)|X15!=k2_zfmisc_1(X13,X14)))&((~r2_hidden(esk4_3(X22,X23,X24),X24)|(~r2_hidden(X26,X22)|~r2_hidden(X27,X23)|esk4_3(X22,X23,X24)!=k4_tarski(X26,X27))|X24=k2_zfmisc_1(X22,X23))&(((r2_hidden(esk5_3(X22,X23,X24),X22)|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))&(r2_hidden(esk6_3(X22,X23,X24),X23)|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23)))&(esk4_3(X22,X23,X24)=k4_tarski(esk5_3(X22,X23,X24),esk6_3(X22,X23,X24))|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.21/0.38  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.38  cnf(c_0_9, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.38  cnf(c_0_10, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  cnf(c_0_11, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.21/0.38  cnf(c_0_12, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_13, plain, (~r2_hidden(esk3_4(X1,k1_xboole_0,k2_zfmisc_1(X1,k1_xboole_0),X2),X3)|~r2_hidden(X2,k2_zfmisc_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.38  fof(c_0_14, plain, ![X10]:(X10=k1_xboole_0|r2_hidden(esk1_1(X10),X10)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.21/0.38  cnf(c_0_16, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_13, c_0_12])).
% 0.21/0.38  cnf(c_0_17, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_18, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  fof(c_0_19, negated_conjecture, (((esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0)&(esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0))&(k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|(esk7_0=k1_xboole_0|esk8_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.21/0.38  cnf(c_0_20, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.21/0.38  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_23, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_16, c_0_20])).
% 0.21/0.38  cnf(c_0_24, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k4_tarski(X1,X2),k1_xboole_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.38  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk4_3(X2,k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20])).
% 0.21/0.38  cnf(c_0_27, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_23])).
% 0.21/0.38  cnf(c_0_29, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.21/0.38  cnf(c_0_32, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_20])])).
% 0.21/0.38  cnf(c_0_35, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_17])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_34])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 37
% 0.21/0.38  # Proof object clause steps            : 26
% 0.21/0.38  # Proof object formula steps           : 11
% 0.21/0.38  # Proof object conjectures             : 11
% 0.21/0.38  # Proof object clause conjectures      : 8
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 10
% 0.21/0.38  # Proof object initial formulas used   : 5
% 0.21/0.38  # Proof object generating inferences   : 11
% 0.21/0.38  # Proof object simplifying inferences  : 13
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 5
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 17
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 17
% 0.21/0.38  # Processed clauses                    : 57
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 5
% 0.21/0.38  # ...remaining for further processing  : 52
% 0.21/0.38  # Other redundant clauses eliminated   : 5
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 5
% 0.21/0.38  # Backward-rewritten                   : 6
% 0.21/0.38  # Generated clauses                    : 108
% 0.21/0.38  # ...of the previous two non-trivial   : 108
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 104
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 5
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 20
% 0.21/0.38  #    Positive orientable unit clauses  : 4
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 15
% 0.21/0.38  # Current number of unprocessed clauses: 77
% 0.21/0.38  # ...number of literals in the above   : 268
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 28
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 60
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 30
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.21/0.38  # Unit Clause-clause subsumption calls : 6
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 4
% 0.21/0.38  # BW rewrite match successes           : 4
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2731
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.031 s
% 0.21/0.38  # System time              : 0.003 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
