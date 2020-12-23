%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:07 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 705 expanded)
%              Number of clauses        :   36 ( 320 expanded)
%              Number of leaves         :    4 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 (2448 expanded)
%              Number of equality atoms :  107 (2065 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t75_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_4,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r1_tarski(X7,k2_tarski(X8,X9))
        | X7 = k1_xboole_0
        | X7 = k1_tarski(X8)
        | X7 = k1_tarski(X9)
        | X7 = k2_tarski(X8,X9) )
      & ( X7 != k1_xboole_0
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k1_tarski(X8)
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k1_tarski(X9)
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k2_tarski(X8,X9)
        | r1_tarski(X7,k2_tarski(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_5,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
      <=> ~ ( X1 != k1_xboole_0
            & X1 != k1_tarski(X2)
            & X1 != k1_tarski(X3)
            & X1 != k2_tarski(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t75_zfmisc_1])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( k4_xboole_0(X4,X5) != k1_xboole_0
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | k4_xboole_0(X4,X5) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_11,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk2_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k2_tarski(esk2_0,esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
      | esk1_0 = k1_xboole_0
      | esk1_0 = k1_tarski(esk2_0)
      | esk1_0 = k1_tarski(esk3_0)
      | esk1_0 = k2_tarski(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X3,X3)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X2,X2)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_8]),c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0)
    | esk1_0 = k1_tarski(esk3_0)
    | esk1_0 = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X1 = k2_tarski(X2,X2)
    | X1 = k2_tarski(X3,X2)
    | X1 = k2_tarski(X3,X3)
    | X1 = k1_xboole_0
    | k4_xboole_0(X1,k2_tarski(X3,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = k2_tarski(esk2_0,esk2_0)
    | esk1_0 = k2_tarski(esk2_0,esk3_0)
    | esk1_0 = k2_tarski(esk3_0,esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_8]),c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != k1_tarski(esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = esk1_0
    | k2_tarski(esk2_0,esk3_0) = esk1_0
    | k2_tarski(esk3_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != k2_tarski(esk3_0,esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(X1,esk3_0)) = k1_xboole_0
    | k2_tarski(esk2_0,esk3_0) = esk1_0
    | k2_tarski(esk2_0,esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_8])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k2_tarski(esk2_0,esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = esk1_0
    | k2_tarski(esk2_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0
    | k4_xboole_0(esk1_0,esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_33])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_38,negated_conjecture,
    ( esk1_0 != k2_tarski(esk2_0,esk2_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,X1)) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:25:57 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.15/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.027 s
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.15/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.38  fof(t75_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 0.15/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.15/0.38  fof(c_0_4, plain, ![X7, X8, X9]:((~r1_tarski(X7,k2_tarski(X8,X9))|(X7=k1_xboole_0|X7=k1_tarski(X8)|X7=k1_tarski(X9)|X7=k2_tarski(X8,X9)))&((((X7!=k1_xboole_0|r1_tarski(X7,k2_tarski(X8,X9)))&(X7!=k1_tarski(X8)|r1_tarski(X7,k2_tarski(X8,X9))))&(X7!=k1_tarski(X9)|r1_tarski(X7,k2_tarski(X8,X9))))&(X7!=k2_tarski(X8,X9)|r1_tarski(X7,k2_tarski(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.15/0.38  fof(c_0_5, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t75_zfmisc_1])).
% 0.15/0.38  cnf(c_0_7, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.15/0.38  cnf(c_0_8, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.15/0.38  cnf(c_0_9, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.15/0.38  fof(c_0_10, plain, ![X4, X5]:((k4_xboole_0(X4,X5)!=k1_xboole_0|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|k4_xboole_0(X4,X5)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.15/0.38  fof(c_0_11, negated_conjecture, (((((esk1_0!=k1_xboole_0|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0)&(esk1_0!=k1_tarski(esk2_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0))&(esk1_0!=k1_tarski(esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0))&(esk1_0!=k2_tarski(esk2_0,esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0))&(k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))=k1_xboole_0|(esk1_0=k1_xboole_0|esk1_0=k1_tarski(esk2_0)|esk1_0=k1_tarski(esk3_0)|esk1_0=k2_tarski(esk2_0,esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.15/0.38  cnf(c_0_12, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_7, c_0_8])).
% 0.15/0.38  cnf(c_0_13, plain, (X1=k1_xboole_0|X1=k2_tarski(X3,X3)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X2,X2)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_8]), c_0_8])).
% 0.15/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.38  cnf(c_0_15, negated_conjecture, (k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))=k1_xboole_0|esk1_0=k1_xboole_0|esk1_0=k1_tarski(esk2_0)|esk1_0=k1_tarski(esk3_0)|esk1_0=k2_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.38  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.38  cnf(c_0_17, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X1))), inference(er,[status(thm)],[c_0_12])).
% 0.15/0.38  cnf(c_0_18, plain, (X1=k2_tarski(X2,X2)|X1=k2_tarski(X3,X2)|X1=k2_tarski(X3,X3)|X1=k1_xboole_0|k4_xboole_0(X1,k2_tarski(X3,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.15/0.38  cnf(c_0_19, negated_conjecture, (esk1_0=k1_xboole_0|esk1_0=k2_tarski(esk2_0,esk2_0)|esk1_0=k2_tarski(esk2_0,esk3_0)|esk1_0=k2_tarski(esk3_0,esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_8]), c_0_8])).
% 0.15/0.38  cnf(c_0_20, negated_conjecture, (esk1_0!=k1_tarski(esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.38  cnf(c_0_21, plain, (k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.15/0.38  cnf(c_0_22, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=esk1_0|k2_tarski(esk2_0,esk3_0)=esk1_0|k2_tarski(esk3_0,esk3_0)=esk1_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.15/0.38  cnf(c_0_23, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.15/0.38  cnf(c_0_24, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.15/0.38  cnf(c_0_25, negated_conjecture, (esk1_0!=k2_tarski(esk3_0,esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_8])).
% 0.15/0.38  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk1_0,k2_tarski(X1,esk3_0))=k1_xboole_0|k2_tarski(esk2_0,esk3_0)=esk1_0|k2_tarski(esk2_0,esk2_0)=esk1_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.15/0.38  cnf(c_0_27, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_23, c_0_8])).
% 0.15/0.38  cnf(c_0_28, plain, (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.15/0.38  cnf(c_0_29, negated_conjecture, (esk1_0!=k2_tarski(esk2_0,esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.38  cnf(c_0_30, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=esk1_0|k2_tarski(esk2_0,esk3_0)=esk1_0|esk1_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_22])).
% 0.15/0.38  cnf(c_0_31, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.15/0.38  cnf(c_0_32, plain, (k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_28])).
% 0.15/0.38  cnf(c_0_33, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=esk1_0|esk1_0=k1_xboole_0|k4_xboole_0(esk1_0,esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.38  cnf(c_0_34, negated_conjecture, (esk1_0!=k1_tarski(esk2_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.38  cnf(c_0_35, plain, (k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_31])).
% 0.15/0.38  cnf(c_0_36, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=esk1_0|esk1_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_33])).
% 0.15/0.38  cnf(c_0_37, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.15/0.38  cnf(c_0_38, negated_conjecture, (esk1_0!=k2_tarski(esk2_0,esk2_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_8])).
% 0.15/0.38  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk1_0,k2_tarski(esk2_0,X1))=k1_xboole_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.15/0.38  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))), inference(er,[status(thm)],[c_0_37])).
% 0.15/0.38  cnf(c_0_41, negated_conjecture, (esk1_0!=k1_xboole_0|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.38  cnf(c_0_42, negated_conjecture, (esk1_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_36])).
% 0.15/0.38  cnf(c_0_43, plain, (k4_xboole_0(k1_xboole_0,k2_tarski(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_40])).
% 0.15/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_42])]), ['proof']).
% 0.15/0.38  # SZS output end CNFRefutation
% 0.15/0.38  # Proof object total steps             : 45
% 0.15/0.38  # Proof object clause steps            : 36
% 0.15/0.38  # Proof object formula steps           : 9
% 0.15/0.38  # Proof object conjectures             : 19
% 0.15/0.38  # Proof object clause conjectures      : 16
% 0.15/0.38  # Proof object formula conjectures     : 3
% 0.15/0.38  # Proof object initial clauses used    : 13
% 0.15/0.38  # Proof object initial formulas used   : 4
% 0.15/0.38  # Proof object generating inferences   : 12
% 0.15/0.38  # Proof object simplifying inferences  : 19
% 0.15/0.38  # Training examples: 0 positive, 0 negative
% 0.15/0.38  # Parsed axioms                        : 4
% 0.15/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.38  # Initial clauses                      : 13
% 0.15/0.38  # Removed in clause preprocessing      : 1
% 0.15/0.38  # Initial clauses in saturation        : 12
% 0.15/0.38  # Processed clauses                    : 71
% 0.15/0.38  # ...of these trivial                  : 0
% 0.15/0.38  # ...subsumed                          : 22
% 0.15/0.38  # ...remaining for further processing  : 49
% 0.15/0.38  # Other redundant clauses eliminated   : 4
% 0.15/0.38  # Clauses deleted for lack of memory   : 0
% 0.15/0.38  # Backward-subsumed                    : 15
% 0.15/0.38  # Backward-rewritten                   : 17
% 0.15/0.38  # Generated clauses                    : 94
% 0.15/0.38  # ...of the previous two non-trivial   : 86
% 0.15/0.38  # Contextual simplify-reflections      : 3
% 0.15/0.38  # Paramodulations                      : 90
% 0.15/0.38  # Factorizations                       : 0
% 0.15/0.38  # Equation resolutions                 : 4
% 0.15/0.38  # Propositional unsat checks           : 0
% 0.15/0.38  #    Propositional check models        : 0
% 0.15/0.38  #    Propositional check unsatisfiable : 0
% 0.15/0.38  #    Propositional clauses             : 0
% 0.15/0.38  #    Propositional clauses after purity: 0
% 0.15/0.38  #    Propositional unsat core size     : 0
% 0.15/0.38  #    Propositional preprocessing time  : 0.000
% 0.15/0.38  #    Propositional encoding time       : 0.000
% 0.15/0.38  #    Propositional solver time         : 0.000
% 0.15/0.38  #    Success case prop preproc time    : 0.000
% 0.15/0.38  #    Success case prop encoding time   : 0.000
% 0.15/0.38  #    Success case prop solver time     : 0.000
% 0.15/0.38  # Current number of processed clauses  : 13
% 0.15/0.38  #    Positive orientable unit clauses  : 9
% 0.15/0.38  #    Positive unorientable unit clauses: 0
% 0.15/0.38  #    Negative unit clauses             : 0
% 0.15/0.38  #    Non-unit-clauses                  : 4
% 0.15/0.38  # Current number of unprocessed clauses: 7
% 0.15/0.38  # ...number of literals in the above   : 22
% 0.15/0.38  # Current number of archived formulas  : 0
% 0.15/0.38  # Current number of archived clauses   : 33
% 0.15/0.38  # Clause-clause subsumption calls (NU) : 89
% 0.15/0.38  # Rec. Clause-clause subsumption calls : 57
% 0.15/0.38  # Non-unit clause-clause subsumptions  : 40
% 0.15/0.38  # Unit Clause-clause subsumption calls : 2
% 0.15/0.38  # Rewrite failures with RHS unbound    : 0
% 0.15/0.38  # BW rewrite match attempts            : 7
% 0.15/0.38  # BW rewrite match successes           : 1
% 0.15/0.38  # Condensation attempts                : 0
% 0.15/0.38  # Condensation successes               : 0
% 0.15/0.38  # Termbank termtop insertions          : 1964
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.028 s
% 0.15/0.38  # System time              : 0.005 s
% 0.15/0.38  # Total time               : 0.033 s
% 0.15/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
