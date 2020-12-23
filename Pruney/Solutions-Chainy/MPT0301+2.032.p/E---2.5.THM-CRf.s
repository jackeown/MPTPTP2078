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
% DateTime   : Thu Dec  3 10:43:29 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 448 expanded)
%              Number of clauses        :   22 ( 207 expanded)
%              Number of leaves         :    5 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 (1797 expanded)
%              Number of equality atoms :   50 ( 488 expanded)
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

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

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

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

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
    ! [X10] : k5_xboole_0(X10,X10) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14,X17,X18,X19,X20,X21,X22,X24,X25] :
      ( ( r2_hidden(esk1_4(X11,X12,X13,X14),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( X14 = k4_tarski(esk1_4(X11,X12,X13,X14),esk2_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(X18,X11)
        | ~ r2_hidden(X19,X12)
        | X17 != k4_tarski(X18,X19)
        | r2_hidden(X17,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X25,X21)
        | esk3_3(X20,X21,X22) != k4_tarski(X24,X25)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk4_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk5_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( esk3_3(X20,X21,X22) = k4_tarski(esk4_3(X20,X21,X22),esk5_3(X20,X21,X22))
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_8]),c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X28,X29,X30,X31] :
      ( ( r2_hidden(X28,X30)
        | ~ r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) )
      & ( r2_hidden(X29,X31)
        | ~ r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) )
      & ( ~ r2_hidden(X28,X30)
        | ~ r2_hidden(X29,X31)
        | r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_16,negated_conjecture,
    ( ( esk6_0 != k1_xboole_0
      | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 )
    & ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
      | esk6_0 = k1_xboole_0
      | esk7_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_17,plain,
    ( X1 = k2_zfmisc_1(k1_xboole_0,X2)
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_20]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:02:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.13/0.37  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.13/0.37  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.13/0.37  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.13/0.37  fof(c_0_5, plain, ![X7, X8, X9]:(((~r2_hidden(X7,X8)|~r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9)))&(r2_hidden(X7,X8)|r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9))))&((~r2_hidden(X7,X8)|r2_hidden(X7,X9)|r2_hidden(X7,k5_xboole_0(X8,X9)))&(~r2_hidden(X7,X9)|r2_hidden(X7,X8)|r2_hidden(X7,k5_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X10]:k5_xboole_0(X10,X10)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.13/0.37  cnf(c_0_7, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_8, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_10, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.37  fof(c_0_11, plain, ![X11, X12, X13, X14, X17, X18, X19, X20, X21, X22, X24, X25]:(((((r2_hidden(esk1_4(X11,X12,X13,X14),X11)|~r2_hidden(X14,X13)|X13!=k2_zfmisc_1(X11,X12))&(r2_hidden(esk2_4(X11,X12,X13,X14),X12)|~r2_hidden(X14,X13)|X13!=k2_zfmisc_1(X11,X12)))&(X14=k4_tarski(esk1_4(X11,X12,X13,X14),esk2_4(X11,X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k2_zfmisc_1(X11,X12)))&(~r2_hidden(X18,X11)|~r2_hidden(X19,X12)|X17!=k4_tarski(X18,X19)|r2_hidden(X17,X13)|X13!=k2_zfmisc_1(X11,X12)))&((~r2_hidden(esk3_3(X20,X21,X22),X22)|(~r2_hidden(X24,X20)|~r2_hidden(X25,X21)|esk3_3(X20,X21,X22)!=k4_tarski(X24,X25))|X22=k2_zfmisc_1(X20,X21))&(((r2_hidden(esk4_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_zfmisc_1(X20,X21))&(r2_hidden(esk5_3(X20,X21,X22),X21)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_zfmisc_1(X20,X21)))&(esk3_3(X20,X21,X22)=k4_tarski(esk4_3(X20,X21,X22),esk5_3(X20,X21,X22))|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.13/0.37  cnf(c_0_13, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_8]), c_0_10])).
% 0.13/0.37  cnf(c_0_14, plain, (r2_hidden(esk4_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_15, plain, ![X28, X29, X30, X31]:(((r2_hidden(X28,X30)|~r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)))&(r2_hidden(X29,X31)|~r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31))))&(~r2_hidden(X28,X30)|~r2_hidden(X29,X31)|r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.13/0.37  fof(c_0_16, negated_conjecture, (((esk6_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0)&(esk7_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0))&(k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|(esk6_0=k1_xboole_0|esk7_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.13/0.37  cnf(c_0_17, plain, (X1=k2_zfmisc_1(k1_xboole_0,X2)|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.37  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_17])).
% 0.13/0.37  cnf(c_0_21, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_13])).
% 0.13/0.37  cnf(c_0_23, plain, (X1=k1_xboole_0|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_17, c_0_20])).
% 0.13/0.37  cnf(c_0_24, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.37  cnf(c_0_26, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_13, c_0_24])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.13/0.37  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (esk6_0!=k1_xboole_0|k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_20]), c_0_31])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 33
% 0.13/0.37  # Proof object clause steps            : 22
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 9
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 10
% 0.13/0.37  # Proof object simplifying inferences  : 10
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 19
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 19
% 0.13/0.37  # Processed clauses                    : 129
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 55
% 0.13/0.37  # ...remaining for further processing  : 74
% 0.13/0.37  # Other redundant clauses eliminated   : 5
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 10
% 0.13/0.37  # Backward-rewritten                   : 18
% 0.13/0.37  # Generated clauses                    : 316
% 0.13/0.37  # ...of the previous two non-trivial   : 327
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 312
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 5
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 24
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 19
% 0.13/0.37  # Current number of unprocessed clauses: 213
% 0.13/0.37  # ...number of literals in the above   : 671
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 46
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 134
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 86
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.37  # Unit Clause-clause subsumption calls : 39
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 7
% 0.13/0.37  # BW rewrite match successes           : 7
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 5094
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.007 s
% 0.13/0.37  # Total time               : 0.037 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
