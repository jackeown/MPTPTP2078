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
% DateTime   : Thu Dec  3 10:44:05 EST 2020

% Result     : Theorem 19.60s
% Output     : CNFRefutation 19.60s
% Verified   : 
% Statistics : Number of formulae       :   31 (  97 expanded)
%              Number of clauses        :   22 (  43 expanded)
%              Number of leaves         :    4 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 279 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
     => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
       => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    inference(assume_negation,[status(cth)],[t137_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,k2_zfmisc_1(X16,X17))
      | k4_tarski(esk2_1(X15),esk3_1(X15)) = X15 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))
    & r2_hidden(esk4_0,k2_zfmisc_1(esk7_0,esk8_0))
    & ~ r2_hidden(esk4_0,k2_zfmisc_1(k3_xboole_0(esk5_0,esk7_0),k3_xboole_0(esk6_0,esk8_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X21,X23)
        | r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_8,plain,
    ( k4_tarski(esk2_1(X1),esk3_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k4_tarski(esk2_1(esk4_0),esk3_1(esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),X1)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),X1)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k3_xboole_0(X1,esk7_0))
    | ~ r2_hidden(esk2_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_9])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k3_xboole_0(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),k3_xboole_0(X1,esk8_0))
    | ~ r2_hidden(esk3_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk4_0),X1),k2_zfmisc_1(k3_xboole_0(esk5_0,esk7_0),X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),k3_xboole_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k2_zfmisc_1(k3_xboole_0(esk5_0,esk7_0),k3_xboole_0(esk6_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_12]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:02:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 19.60/19.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 19.60/19.78  # and selection function SelectDivPreferIntoLits.
% 19.60/19.78  #
% 19.60/19.78  # Preprocessing time       : 0.027 s
% 19.60/19.78  # Presaturation interreduction done
% 19.60/19.78  
% 19.60/19.78  # Proof found!
% 19.60/19.78  # SZS status Theorem
% 19.60/19.78  # SZS output start CNFRefutation
% 19.60/19.78  fof(t137_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5]:((r2_hidden(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X1,k2_zfmisc_1(X4,X5)))=>r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_zfmisc_1)).
% 19.60/19.78  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 19.60/19.78  fof(t106_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 19.60/19.78  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 19.60/19.78  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5]:((r2_hidden(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X1,k2_zfmisc_1(X4,X5)))=>r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))))), inference(assume_negation,[status(cth)],[t137_zfmisc_1])).
% 19.60/19.78  fof(c_0_5, plain, ![X15, X16, X17]:(~r2_hidden(X15,k2_zfmisc_1(X16,X17))|k4_tarski(esk2_1(X15),esk3_1(X15))=X15), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 19.60/19.78  fof(c_0_6, negated_conjecture, ((r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))&r2_hidden(esk4_0,k2_zfmisc_1(esk7_0,esk8_0)))&~r2_hidden(esk4_0,k2_zfmisc_1(k3_xboole_0(esk5_0,esk7_0),k3_xboole_0(esk6_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 19.60/19.78  fof(c_0_7, plain, ![X20, X21, X22, X23]:(((r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))&(r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23))))&(~r2_hidden(X20,X22)|~r2_hidden(X21,X23)|r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).
% 19.60/19.78  cnf(c_0_8, plain, (k4_tarski(esk2_1(X1),esk3_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 19.60/19.78  cnf(c_0_9, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 19.60/19.78  fof(c_0_10, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 19.60/19.78  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 19.60/19.78  cnf(c_0_12, negated_conjecture, (k4_tarski(esk2_1(esk4_0),esk3_1(esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 19.60/19.78  cnf(c_0_13, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 19.60/19.78  cnf(c_0_14, negated_conjecture, (r2_hidden(esk2_1(esk4_0),X1)|~r2_hidden(esk4_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 19.60/19.78  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 19.60/19.78  cnf(c_0_16, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_13])).
% 19.60/19.78  cnf(c_0_17, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk7_0)), inference(spm,[status(thm)],[c_0_14, c_0_9])).
% 19.60/19.78  cnf(c_0_18, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 19.60/19.78  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_1(esk4_0),X1)|~r2_hidden(esk4_0,k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 19.60/19.78  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k3_xboole_0(X1,esk7_0))|~r2_hidden(esk2_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 19.60/19.78  cnf(c_0_21, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 19.60/19.78  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_1(esk4_0),esk8_0)), inference(spm,[status(thm)],[c_0_19, c_0_9])).
% 19.60/19.78  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 19.60/19.78  cnf(c_0_24, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k3_xboole_0(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 19.60/19.78  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_1(esk4_0),k3_xboole_0(X1,esk8_0))|~r2_hidden(esk3_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_16, c_0_22])).
% 19.60/19.78  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_1(esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 19.60/19.78  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk4_0),X1),k2_zfmisc_1(k3_xboole_0(esk5_0,esk7_0),X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 19.60/19.78  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_1(esk4_0),k3_xboole_0(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 19.60/19.78  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk4_0,k2_zfmisc_1(k3_xboole_0(esk5_0,esk7_0),k3_xboole_0(esk6_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 19.60/19.78  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_12]), c_0_29]), ['proof']).
% 19.60/19.78  # SZS output end CNFRefutation
% 19.60/19.78  # Proof object total steps             : 31
% 19.60/19.78  # Proof object clause steps            : 22
% 19.60/19.78  # Proof object formula steps           : 9
% 19.60/19.78  # Proof object conjectures             : 19
% 19.60/19.78  # Proof object clause conjectures      : 16
% 19.60/19.78  # Proof object formula conjectures     : 3
% 19.60/19.78  # Proof object initial clauses used    : 8
% 19.60/19.78  # Proof object initial formulas used   : 4
% 19.60/19.78  # Proof object generating inferences   : 13
% 19.60/19.78  # Proof object simplifying inferences  : 3
% 19.60/19.78  # Training examples: 0 positive, 0 negative
% 19.60/19.78  # Parsed axioms                        : 4
% 19.60/19.78  # Removed by relevancy pruning/SinE    : 0
% 19.60/19.78  # Initial clauses                      : 13
% 19.60/19.78  # Removed in clause preprocessing      : 0
% 19.60/19.78  # Initial clauses in saturation        : 13
% 19.60/19.78  # Processed clauses                    : 5187
% 19.60/19.78  # ...of these trivial                  : 9
% 19.60/19.78  # ...subsumed                          : 540
% 19.60/19.78  # ...remaining for further processing  : 4638
% 19.60/19.78  # Other redundant clauses eliminated   : 3
% 19.60/19.78  # Clauses deleted for lack of memory   : 583424
% 19.60/19.78  # Backward-subsumed                    : 11
% 19.60/19.78  # Backward-rewritten                   : 742
% 19.60/19.78  # Generated clauses                    : 2730089
% 19.60/19.78  # ...of the previous two non-trivial   : 2716048
% 19.60/19.78  # Contextual simplify-reflections      : 3
% 19.60/19.78  # Paramodulations                      : 2729726
% 19.60/19.78  # Factorizations                       : 360
% 19.60/19.78  # Equation resolutions                 : 3
% 19.60/19.78  # Propositional unsat checks           : 0
% 19.60/19.78  #    Propositional check models        : 0
% 19.60/19.78  #    Propositional check unsatisfiable : 0
% 19.60/19.78  #    Propositional clauses             : 0
% 19.60/19.78  #    Propositional clauses after purity: 0
% 19.60/19.78  #    Propositional unsat core size     : 0
% 19.60/19.78  #    Propositional preprocessing time  : 0.000
% 19.60/19.78  #    Propositional encoding time       : 0.000
% 19.60/19.78  #    Propositional solver time         : 0.000
% 19.60/19.78  #    Success case prop preproc time    : 0.000
% 19.60/19.78  #    Success case prop encoding time   : 0.000
% 19.60/19.78  #    Success case prop solver time     : 0.000
% 19.60/19.78  # Current number of processed clauses  : 3869
% 19.60/19.78  #    Positive orientable unit clauses  : 2666
% 19.60/19.78  #    Positive unorientable unit clauses: 0
% 19.60/19.78  #    Negative unit clauses             : 1
% 19.60/19.78  #    Non-unit-clauses                  : 1202
% 19.60/19.78  # Current number of unprocessed clauses: 1650853
% 19.60/19.78  # ...number of literals in the above   : 2813593
% 19.60/19.78  # Current number of archived formulas  : 0
% 19.60/19.78  # Current number of archived clauses   : 766
% 19.60/19.78  # Clause-clause subsumption calls (NU) : 188539
% 19.60/19.78  # Rec. Clause-clause subsumption calls : 138446
% 19.60/19.78  # Non-unit clause-clause subsumptions  : 554
% 19.60/19.78  # Unit Clause-clause subsumption calls : 130779
% 19.60/19.78  # Rewrite failures with RHS unbound    : 0
% 19.60/19.78  # BW rewrite match attempts            : 241566
% 19.60/19.78  # BW rewrite match successes           : 2
% 19.60/19.78  # Condensation attempts                : 0
% 19.60/19.78  # Condensation successes               : 0
% 19.60/19.78  # Termbank termtop insertions          : 87266374
% 19.60/19.85  
% 19.60/19.85  # -------------------------------------------------
% 19.60/19.85  # User time                : 18.606 s
% 19.60/19.85  # System time              : 0.902 s
% 19.60/19.85  # Total time               : 19.508 s
% 19.60/19.85  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
