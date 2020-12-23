%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (1046 expanded)
%              Number of clauses        :   26 ( 458 expanded)
%              Number of leaves         :    6 ( 257 expanded)
%              Depth                    :   14
%              Number of atoms          :  105 (2510 expanded)
%              Number of equality atoms :  104 (2509 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t58_mcart_1])).

fof(c_0_7,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0) = k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18] : k4_zfmisc_1(X15,X16,X17,X18) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17),X18) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ( X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k3_zfmisc_1(X12,X13,X14) != k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k3_zfmisc_1(X12,X13,X14) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k3_zfmisc_1(X12,X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k3_zfmisc_1(X12,X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

fof(c_0_10,plain,(
    ! [X9,X10,X11] : k3_zfmisc_1(X9,X10,X11) = k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8] :
      ( ( X5 = X7
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0
        | k2_zfmisc_1(X5,X6) != k2_zfmisc_1(X7,X8) )
      & ( X6 = X8
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0
        | k2_zfmisc_1(X5,X6) != k2_zfmisc_1(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_12,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0) = k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | k4_zfmisc_1(X19,X20,X21,X22) != k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k4_zfmisc_1(X19,X20,X21,X22) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k4_zfmisc_1(X19,X20,X21,X22) = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k4_zfmisc_1(X19,X20,X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k4_zfmisc_1(X19,X20,X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13])).

cnf(c_0_19,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk1_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_13])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk1_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk1_0 = X1
    | k2_zfmisc_1(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk1_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = X1
    | k2_zfmisc_1(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_29])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_22])).

cnf(c_0_33,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_32]),c_0_32]),c_0_26]),c_0_32]),c_0_26]),c_0_32]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_26])]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:28:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t58_mcart_1, conjecture, ![X1, X2]:(k4_zfmisc_1(X1,X1,X1,X1)=k4_zfmisc_1(X2,X2,X2,X2)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 0.20/0.38  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.20/0.38  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.20/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.38  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.20/0.38  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.20/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(k4_zfmisc_1(X1,X1,X1,X1)=k4_zfmisc_1(X2,X2,X2,X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t58_mcart_1])).
% 0.20/0.38  fof(c_0_7, negated_conjecture, (k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0)=k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)&esk1_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X15, X16, X17, X18]:k4_zfmisc_1(X15,X16,X17,X18)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17),X18), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.20/0.38  fof(c_0_9, plain, ![X12, X13, X14]:((X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0|k3_zfmisc_1(X12,X13,X14)!=k1_xboole_0)&(((X12!=k1_xboole_0|k3_zfmisc_1(X12,X13,X14)=k1_xboole_0)&(X13!=k1_xboole_0|k3_zfmisc_1(X12,X13,X14)=k1_xboole_0))&(X14!=k1_xboole_0|k3_zfmisc_1(X12,X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X9, X10, X11]:k3_zfmisc_1(X9,X10,X11)=k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X5, X6, X7, X8]:((X5=X7|(X5=k1_xboole_0|X6=k1_xboole_0)|k2_zfmisc_1(X5,X6)!=k2_zfmisc_1(X7,X8))&(X6=X8|(X5=k1_xboole_0|X6=k1_xboole_0)|k2_zfmisc_1(X5,X6)!=k2_zfmisc_1(X7,X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0)=k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_13, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_14, plain, ![X19, X20, X21, X22]:((X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0|k4_zfmisc_1(X19,X20,X21,X22)!=k1_xboole_0)&((((X19!=k1_xboole_0|k4_zfmisc_1(X19,X20,X21,X22)=k1_xboole_0)&(X20!=k1_xboole_0|k4_zfmisc_1(X19,X20,X21,X22)=k1_xboole_0))&(X21!=k1_xboole_0|k4_zfmisc_1(X19,X20,X21,X22)=k1_xboole_0))&(X22!=k1_xboole_0|k4_zfmisc_1(X19,X20,X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.20/0.38  cnf(c_0_15, plain, (k3_zfmisc_1(X2,X3,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_16, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_17, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0),esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13])).
% 0.20/0.38  cnf(c_0_19, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_20, plain, (k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)=k1_xboole_0|esk1_0=k1_xboole_0|esk1_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_23, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_13])).
% 0.20/0.38  cnf(c_0_24, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)=k1_xboole_0|esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22])).
% 0.20/0.38  cnf(c_0_26, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_24])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(esk1_0,esk1_0)=k1_xboole_0|esk1_0=k1_xboole_0|esk1_0=X1|k2_zfmisc_1(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0)=k1_xboole_0|esk1_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_26])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(esk1_0,esk1_0)=k1_xboole_0|esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_22])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (esk1_0=k1_xboole_0|esk1_0=X1|k2_zfmisc_1(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_29])).
% 0.20/0.38  cnf(c_0_31, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_22])).
% 0.20/0.38  cnf(c_0_33, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_16])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0),esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_32]), c_0_32]), c_0_26]), c_0_32]), c_0_26]), c_0_32]), c_0_26])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_32])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(esk2_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (X1=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_36]), c_0_26])]), c_0_35])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_37])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 39
% 0.20/0.38  # Proof object clause steps            : 26
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 18
% 0.20/0.38  # Proof object clause conjectures      : 15
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 8
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 9
% 0.20/0.38  # Proof object simplifying inferences  : 26
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 15
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 13
% 0.20/0.38  # Processed clauses                    : 36
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 36
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 17
% 0.20/0.38  # Generated clauses                    : 74
% 0.20/0.38  # ...of the previous two non-trivial   : 59
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 64
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 10
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 1
% 0.20/0.38  #    Positive orientable unit clauses  : 0
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 0
% 0.20/0.38  # Current number of unprocessed clauses: 33
% 0.20/0.38  # ...number of literals in the above   : 128
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 30
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 28
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 13
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 3
% 0.20/0.38  # BW rewrite match attempts            : 18
% 0.20/0.38  # BW rewrite match successes           : 18
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1495
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.028 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.033 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
