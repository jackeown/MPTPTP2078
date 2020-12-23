%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:37 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 440 expanded)
%              Number of clauses        :   30 ( 210 expanded)
%              Number of leaves         :    5 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :   84 ( 795 expanded)
%              Number of equality atoms :   83 ( 794 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(t28_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
       => ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ),
    inference(assume_negation,[status(cth)],[t33_mcart_1])).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19] : k4_mcart_1(X16,X17,X18,X19) = k4_tarski(k3_mcart_1(X16,X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] : k3_mcart_1(X13,X14,X15) = k4_tarski(k4_tarski(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | k4_tarski(X9,X10) != k4_tarski(X11,X12) )
      & ( X10 = X12
        | k4_tarski(X9,X10) != k4_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_12,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) = k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( X20 = X23
        | k3_mcart_1(X20,X21,X22) != k3_mcart_1(X23,X24,X25) )
      & ( X21 = X24
        | k3_mcart_1(X20,X21,X22) != k3_mcart_1(X23,X24,X25) )
      & ( X22 = X25
        | k3_mcart_1(X20,X21,X22) != k3_mcart_1(X23,X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 = X1
    | k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( X1 = X2
    | k3_mcart_1(X3,X1,X4) != k3_mcart_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 = esk8_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( X1 = X2
    | k4_tarski(k4_tarski(X3,X1),X4) != k4_tarski(k4_tarski(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_10]),c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk8_0) = k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( X1 = esk3_0
    | k4_tarski(k4_tarski(X2,X1),X3) != k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = esk7_0 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_24,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0),esk8_0) = k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_26,plain,
    ( X1 = X2
    | k3_mcart_1(X1,X3,X4) != k3_mcart_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0) = X1
    | k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( X1 = X2
    | k4_tarski(k4_tarski(X1,X3),X4) != k4_tarski(k4_tarski(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_10]),c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0) = k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 = X1
    | k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) != k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 = esk5_0 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(k4_tarski(esk5_0,esk2_0),esk7_0) = k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(esk5_0,esk2_0) = X1
    | k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_19])])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(esk5_0,esk2_0) = k4_tarski(esk5_0,esk6_0) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 = X1
    | k4_tarski(esk5_0,esk6_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_31])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.27  % Computer   : n025.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 13:15:05 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  # Version: 2.5pre002
% 0.07/0.27  # No SInE strategy applied
% 0.07/0.27  # Trying AutoSched0 for 299 seconds
% 0.07/0.29  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.07/0.29  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.07/0.29  #
% 0.07/0.29  # Preprocessing time       : 0.015 s
% 0.07/0.29  # Presaturation interreduction done
% 0.07/0.29  
% 0.07/0.29  # Proof found!
% 0.07/0.29  # SZS status Theorem
% 0.07/0.29  # SZS output start CNFRefutation
% 0.07/0.29  fof(t33_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 0.07/0.29  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.07/0.29  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.07/0.29  fof(t33_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k4_tarski(X1,X2)=k4_tarski(X3,X4)=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 0.07/0.29  fof(t28_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_mcart_1(X1,X2,X3)=k3_mcart_1(X4,X5,X6)=>((X1=X4&X2=X5)&X3=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 0.07/0.29  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8))), inference(assume_negation,[status(cth)],[t33_mcart_1])).
% 0.07/0.29  fof(c_0_6, plain, ![X16, X17, X18, X19]:k4_mcart_1(X16,X17,X18,X19)=k4_tarski(k3_mcart_1(X16,X17,X18),X19), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.07/0.29  fof(c_0_7, plain, ![X13, X14, X15]:k3_mcart_1(X13,X14,X15)=k4_tarski(k4_tarski(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.07/0.29  fof(c_0_8, negated_conjecture, (k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.07/0.29  cnf(c_0_9, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.07/0.29  cnf(c_0_10, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.07/0.29  fof(c_0_11, plain, ![X9, X10, X11, X12]:((X9=X11|k4_tarski(X9,X10)!=k4_tarski(X11,X12))&(X10=X12|k4_tarski(X9,X10)!=k4_tarski(X11,X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).
% 0.07/0.29  cnf(c_0_12, negated_conjecture, (k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.07/0.29  cnf(c_0_13, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.07/0.29  cnf(c_0_14, plain, (X1=X2|k4_tarski(X3,X1)!=k4_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.29  cnf(c_0_15, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)=k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13])).
% 0.07/0.29  fof(c_0_16, plain, ![X20, X21, X22, X23, X24, X25]:(((X20=X23|k3_mcart_1(X20,X21,X22)!=k3_mcart_1(X23,X24,X25))&(X21=X24|k3_mcart_1(X20,X21,X22)!=k3_mcart_1(X23,X24,X25)))&(X22=X25|k3_mcart_1(X20,X21,X22)!=k3_mcart_1(X23,X24,X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).
% 0.07/0.29  cnf(c_0_17, negated_conjecture, (esk4_0=X1|k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)!=k4_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.07/0.29  cnf(c_0_18, plain, (X1=X2|k3_mcart_1(X3,X1,X4)!=k3_mcart_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.07/0.29  cnf(c_0_19, negated_conjecture, (esk4_0=esk8_0), inference(er,[status(thm)],[c_0_17])).
% 0.07/0.29  cnf(c_0_20, plain, (X1=X2|k4_tarski(k4_tarski(X3,X1),X4)!=k4_tarski(k4_tarski(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_10]), c_0_10])).
% 0.07/0.29  cnf(c_0_21, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk8_0)=k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)), inference(rw,[status(thm)],[c_0_15, c_0_19])).
% 0.07/0.29  cnf(c_0_22, negated_conjecture, (X1=esk3_0|k4_tarski(k4_tarski(X2,X1),X3)!=k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.07/0.29  cnf(c_0_23, negated_conjecture, (esk3_0=esk7_0), inference(er,[status(thm)],[c_0_22])).
% 0.07/0.29  cnf(c_0_24, plain, (X1=X2|k4_tarski(X1,X3)!=k4_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.29  cnf(c_0_25, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0),esk8_0)=k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)), inference(rw,[status(thm)],[c_0_21, c_0_23])).
% 0.07/0.29  cnf(c_0_26, plain, (X1=X2|k3_mcart_1(X1,X3,X4)!=k3_mcart_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.07/0.29  cnf(c_0_27, negated_conjecture, (k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0)=X1|k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)!=k4_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.07/0.29  cnf(c_0_28, plain, (X1=X2|k4_tarski(k4_tarski(X1,X3),X4)!=k4_tarski(k4_tarski(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_10]), c_0_10])).
% 0.07/0.29  cnf(c_0_29, negated_conjecture, (k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0)=k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)), inference(er,[status(thm)],[c_0_27])).
% 0.07/0.29  cnf(c_0_30, negated_conjecture, (esk1_0=X1|k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)!=k4_tarski(k4_tarski(X1,X2),X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.07/0.29  cnf(c_0_31, negated_conjecture, (esk1_0=esk5_0), inference(er,[status(thm)],[c_0_30])).
% 0.07/0.29  cnf(c_0_32, negated_conjecture, (k4_tarski(k4_tarski(esk5_0,esk2_0),esk7_0)=k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_29, c_0_31])).
% 0.07/0.29  cnf(c_0_33, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.07/0.29  cnf(c_0_34, negated_conjecture, (k4_tarski(esk5_0,esk2_0)=X1|k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)!=k4_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.07/0.29  cnf(c_0_35, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_19])])).
% 0.07/0.29  cnf(c_0_36, negated_conjecture, (k4_tarski(esk5_0,esk2_0)=k4_tarski(esk5_0,esk6_0)), inference(er,[status(thm)],[c_0_34])).
% 0.07/0.29  cnf(c_0_37, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_23])])).
% 0.07/0.29  cnf(c_0_38, negated_conjecture, (esk2_0=X1|k4_tarski(esk5_0,esk6_0)!=k4_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_14, c_0_36])).
% 0.07/0.29  cnf(c_0_39, negated_conjecture, (esk2_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_31])])).
% 0.07/0.29  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_39]), ['proof']).
% 0.07/0.29  # SZS output end CNFRefutation
% 0.07/0.29  # Proof object total steps             : 41
% 0.07/0.29  # Proof object clause steps            : 30
% 0.07/0.29  # Proof object formula steps           : 11
% 0.07/0.29  # Proof object conjectures             : 24
% 0.07/0.29  # Proof object clause conjectures      : 21
% 0.07/0.29  # Proof object formula conjectures     : 3
% 0.07/0.29  # Proof object initial clauses used    : 8
% 0.07/0.29  # Proof object initial formulas used   : 5
% 0.07/0.29  # Proof object generating inferences   : 12
% 0.07/0.29  # Proof object simplifying inferences  : 17
% 0.07/0.29  # Training examples: 0 positive, 0 negative
% 0.07/0.29  # Parsed axioms                        : 5
% 0.07/0.29  # Removed by relevancy pruning/SinE    : 0
% 0.07/0.29  # Initial clauses                      : 9
% 0.07/0.29  # Removed in clause preprocessing      : 2
% 0.07/0.29  # Initial clauses in saturation        : 7
% 0.07/0.29  # Processed clauses                    : 41
% 0.07/0.29  # ...of these trivial                  : 0
% 0.07/0.29  # ...subsumed                          : 12
% 0.07/0.29  # ...remaining for further processing  : 29
% 0.07/0.29  # Other redundant clauses eliminated   : 0
% 0.07/0.29  # Clauses deleted for lack of memory   : 0
% 0.07/0.29  # Backward-subsumed                    : 0
% 0.07/0.29  # Backward-rewritten                   : 13
% 0.07/0.29  # Generated clauses                    : 76
% 0.07/0.29  # ...of the previous two non-trivial   : 82
% 0.07/0.29  # Contextual simplify-reflections      : 0
% 0.07/0.29  # Paramodulations                      : 66
% 0.07/0.29  # Factorizations                       : 0
% 0.07/0.29  # Equation resolutions                 : 10
% 0.07/0.29  # Propositional unsat checks           : 0
% 0.07/0.29  #    Propositional check models        : 0
% 0.07/0.29  #    Propositional check unsatisfiable : 0
% 0.07/0.29  #    Propositional clauses             : 0
% 0.07/0.29  #    Propositional clauses after purity: 0
% 0.07/0.29  #    Propositional unsat core size     : 0
% 0.07/0.29  #    Propositional preprocessing time  : 0.000
% 0.07/0.29  #    Propositional encoding time       : 0.000
% 0.07/0.29  #    Propositional solver time         : 0.000
% 0.07/0.29  #    Success case prop preproc time    : 0.000
% 0.07/0.29  #    Success case prop encoding time   : 0.000
% 0.07/0.29  #    Success case prop solver time     : 0.000
% 0.07/0.29  # Current number of processed clauses  : 10
% 0.07/0.29  #    Positive orientable unit clauses  : 4
% 0.07/0.29  #    Positive unorientable unit clauses: 0
% 0.07/0.29  #    Negative unit clauses             : 1
% 0.07/0.29  #    Non-unit-clauses                  : 5
% 0.07/0.29  # Current number of unprocessed clauses: 43
% 0.07/0.29  # ...number of literals in the above   : 86
% 0.07/0.29  # Current number of archived formulas  : 0
% 0.07/0.29  # Current number of archived clauses   : 21
% 0.07/0.29  # Clause-clause subsumption calls (NU) : 61
% 0.07/0.29  # Rec. Clause-clause subsumption calls : 61
% 0.07/0.29  # Non-unit clause-clause subsumptions  : 12
% 0.07/0.29  # Unit Clause-clause subsumption calls : 0
% 0.07/0.29  # Rewrite failures with RHS unbound    : 0
% 0.07/0.29  # BW rewrite match attempts            : 5
% 0.07/0.29  # BW rewrite match successes           : 5
% 0.07/0.29  # Condensation attempts                : 0
% 0.07/0.29  # Condensation successes               : 0
% 0.07/0.29  # Termbank termtop insertions          : 1425
% 0.07/0.29  
% 0.07/0.29  # -------------------------------------------------
% 0.07/0.29  # User time                : 0.014 s
% 0.07/0.29  # System time              : 0.004 s
% 0.07/0.29  # Total time               : 0.018 s
% 0.07/0.29  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
