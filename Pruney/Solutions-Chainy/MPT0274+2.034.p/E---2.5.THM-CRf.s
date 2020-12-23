%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:00 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   29 (  58 expanded)
%              Number of clauses        :   22 (  29 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 350 expanded)
%              Number of equality atoms :   51 ( 163 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t72_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X14
        | X17 = X15
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( esk2_3(X19,X20,X21) != X19
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( esk2_3(X19,X20,X21) != X20
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | esk2_3(X19,X20,X21) = X19
        | esk2_3(X19,X20,X21) = X20
        | X21 = k2_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_4,plain,(
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

cnf(c_0_5,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
      <=> ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t72_zfmisc_1])).

cnf(c_0_8,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_12,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0)
      | r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk4_0,esk5_0) )
    & ( ~ r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0) )
    & ( ~ r2_hidden(esk4_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( esk1_3(k2_tarski(X1,X2),X3,k2_tarski(X1,X2)) = X2
    | esk1_3(k2_tarski(X1,X2),X3,k2_tarski(X1,X2)) = X1
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( esk1_3(k2_tarski(X1,X2),X3,k2_tarski(X1,X2)) = X2
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    | r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(X1,k2_tarski(esk3_0,esk4_0))
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,k2_tarski(esk3_0,esk4_0))
    | ~ r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    | r2_hidden(X1,X3)
    | r2_hidden(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:23:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.24/2.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 2.24/2.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.24/2.44  #
% 2.24/2.44  # Preprocessing time       : 0.026 s
% 2.24/2.44  # Presaturation interreduction done
% 2.24/2.44  
% 2.24/2.44  # Proof found!
% 2.24/2.44  # SZS status Theorem
% 2.24/2.44  # SZS output start CNFRefutation
% 2.24/2.44  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.24/2.44  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.24/2.44  fof(t72_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.24/2.44  fof(c_0_3, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X17,X16)|(X17=X14|X17=X15)|X16!=k2_tarski(X14,X15))&((X18!=X14|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))))&(((esk2_3(X19,X20,X21)!=X19|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20))&(esk2_3(X19,X20,X21)!=X20|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20)))&(r2_hidden(esk2_3(X19,X20,X21),X21)|(esk2_3(X19,X20,X21)=X19|esk2_3(X19,X20,X21)=X20)|X21=k2_tarski(X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 2.24/2.44  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.24/2.44  cnf(c_0_5, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 2.24/2.44  cnf(c_0_6, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 2.24/2.44  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3))))), inference(assume_negation,[status(cth)],[t72_zfmisc_1])).
% 2.24/2.44  cnf(c_0_8, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_5])).
% 2.24/2.44  cnf(c_0_9, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_6])).
% 2.24/2.44  cnf(c_0_10, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 2.24/2.44  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 2.24/2.44  fof(c_0_12, negated_conjecture, ((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)|(r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)))&((~r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0))&(~r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).
% 2.24/2.44  cnf(c_0_13, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 2.24/2.44  cnf(c_0_14, plain, (esk1_3(k2_tarski(X1,X2),X3,k2_tarski(X1,X2))=X2|esk1_3(k2_tarski(X1,X2),X3,k2_tarski(X1,X2))=X1|k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 2.24/2.44  cnf(c_0_15, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).
% 2.24/2.44  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 2.24/2.44  cnf(c_0_17, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_11])).
% 2.24/2.44  cnf(c_0_18, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.24/2.44  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.24/2.44  cnf(c_0_20, plain, (esk1_3(k2_tarski(X1,X2),X3,k2_tarski(X1,X2))=X2|k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)|r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 2.24/2.44  cnf(c_0_21, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).
% 2.24/2.44  cnf(c_0_22, negated_conjecture, (~r2_hidden(X1,k2_tarski(esk3_0,esk4_0))|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 2.24/2.44  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,k2_tarski(esk3_0,esk4_0))|~r2_hidden(esk4_0,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 2.24/2.44  cnf(c_0_24, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.24/2.44  cnf(c_0_25, plain, (k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)|r2_hidden(X1,X3)|r2_hidden(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_20]), c_0_21])])).
% 2.24/2.44  cnf(c_0_26, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_15])).
% 2.24/2.44  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 2.24/2.44  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), ['proof']).
% 2.24/2.44  # SZS output end CNFRefutation
% 2.24/2.44  # Proof object total steps             : 29
% 2.24/2.44  # Proof object clause steps            : 22
% 2.24/2.44  # Proof object formula steps           : 7
% 2.24/2.44  # Proof object conjectures             : 11
% 2.24/2.44  # Proof object clause conjectures      : 8
% 2.24/2.44  # Proof object formula conjectures     : 3
% 2.24/2.44  # Proof object initial clauses used    : 9
% 2.24/2.44  # Proof object initial formulas used   : 3
% 2.24/2.44  # Proof object generating inferences   : 9
% 2.24/2.44  # Proof object simplifying inferences  : 12
% 2.24/2.44  # Training examples: 0 positive, 0 negative
% 2.24/2.44  # Parsed axioms                        : 3
% 2.24/2.44  # Removed by relevancy pruning/SinE    : 0
% 2.24/2.44  # Initial clauses                      : 15
% 2.24/2.44  # Removed in clause preprocessing      : 0
% 2.24/2.44  # Initial clauses in saturation        : 15
% 2.24/2.44  # Processed clauses                    : 22601
% 2.24/2.44  # ...of these trivial                  : 173
% 2.24/2.44  # ...subsumed                          : 21490
% 2.24/2.44  # ...remaining for further processing  : 938
% 2.24/2.44  # Other redundant clauses eliminated   : 212
% 2.24/2.44  # Clauses deleted for lack of memory   : 0
% 2.24/2.44  # Backward-subsumed                    : 25
% 2.24/2.44  # Backward-rewritten                   : 13
% 2.24/2.44  # Generated clauses                    : 267086
% 2.24/2.44  # ...of the previous two non-trivial   : 245860
% 2.24/2.44  # Contextual simplify-reflections      : 8
% 2.24/2.44  # Paramodulations                      : 266636
% 2.24/2.44  # Factorizations                       : 240
% 2.24/2.44  # Equation resolutions                 : 212
% 2.24/2.44  # Propositional unsat checks           : 0
% 2.24/2.44  #    Propositional check models        : 0
% 2.24/2.44  #    Propositional check unsatisfiable : 0
% 2.24/2.44  #    Propositional clauses             : 0
% 2.24/2.44  #    Propositional clauses after purity: 0
% 2.24/2.44  #    Propositional unsat core size     : 0
% 2.24/2.44  #    Propositional preprocessing time  : 0.000
% 2.24/2.44  #    Propositional encoding time       : 0.000
% 2.24/2.44  #    Propositional solver time         : 0.000
% 2.24/2.44  #    Success case prop preproc time    : 0.000
% 2.24/2.44  #    Success case prop encoding time   : 0.000
% 2.24/2.44  #    Success case prop solver time     : 0.000
% 2.24/2.44  # Current number of processed clauses  : 879
% 2.24/2.44  #    Positive orientable unit clauses  : 62
% 2.24/2.44  #    Positive unorientable unit clauses: 7
% 2.24/2.44  #    Negative unit clauses             : 45
% 2.24/2.44  #    Non-unit-clauses                  : 765
% 2.24/2.44  # Current number of unprocessed clauses: 221897
% 2.24/2.44  # ...number of literals in the above   : 766704
% 2.24/2.44  # Current number of archived formulas  : 0
% 2.24/2.44  # Current number of archived clauses   : 53
% 2.24/2.44  # Clause-clause subsumption calls (NU) : 246152
% 2.24/2.44  # Rec. Clause-clause subsumption calls : 143284
% 2.24/2.44  # Non-unit clause-clause subsumptions  : 9798
% 2.24/2.44  # Unit Clause-clause subsumption calls : 7383
% 2.24/2.44  # Rewrite failures with RHS unbound    : 1045
% 2.24/2.44  # BW rewrite match attempts            : 1711
% 2.24/2.44  # BW rewrite match successes           : 51
% 2.24/2.44  # Condensation attempts                : 0
% 2.24/2.44  # Condensation successes               : 0
% 2.24/2.44  # Termbank termtop insertions          : 4993366
% 2.24/2.45  
% 2.24/2.45  # -------------------------------------------------
% 2.24/2.45  # User time                : 2.022 s
% 2.24/2.45  # System time              : 0.085 s
% 2.24/2.45  # Total time               : 2.107 s
% 2.24/2.45  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
