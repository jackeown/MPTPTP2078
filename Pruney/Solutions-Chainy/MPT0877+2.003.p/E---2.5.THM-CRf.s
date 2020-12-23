%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 159 expanded)
%              Number of clauses        :   27 (  71 expanded)
%              Number of leaves         :    4 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 ( 457 expanded)
%              Number of equality atoms :  124 ( 456 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_mcart_1])).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( X12 = X15
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k3_zfmisc_1(X12,X13,X14) != k3_zfmisc_1(X15,X16,X17) )
      & ( X13 = X16
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k3_zfmisc_1(X12,X13,X14) != k3_zfmisc_1(X15,X16,X17) )
      & ( X14 = X17
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | k3_zfmisc_1(X12,X13,X14) != k3_zfmisc_1(X15,X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] : k3_zfmisc_1(X9,X10,X11) = k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_7,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0)
    & k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) != k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_9]),c_0_9])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_14,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( X1 = esk6_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),X4) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk6_0 = esk3_0
    | X1 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk6_0 = esk3_0
    | esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_20]),c_0_19]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk5_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) != k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_9]),c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != esk1_0
    | esk5_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk5_0 = esk2_0 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( X1 = esk4_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 != esk1_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_31]),c_0_32])])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_33]),c_0_32]),c_0_19])])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_34]),c_0_19]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:52:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t37_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.12/0.38  fof(t36_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.12/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6)))), inference(assume_negation,[status(cth)],[t37_mcart_1])).
% 0.12/0.38  fof(c_0_5, plain, ![X12, X13, X14, X15, X16, X17]:(((X12=X15|(X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)|k3_zfmisc_1(X12,X13,X14)!=k3_zfmisc_1(X15,X16,X17))&(X13=X16|(X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)|k3_zfmisc_1(X12,X13,X14)!=k3_zfmisc_1(X15,X16,X17)))&(X14=X17|(X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)|k3_zfmisc_1(X12,X13,X14)!=k3_zfmisc_1(X15,X16,X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).
% 0.12/0.38  fof(c_0_6, plain, ![X9, X10, X11]:k3_zfmisc_1(X9,X10,X11)=k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.38  fof(c_0_7, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k3_zfmisc_1(esk4_0,esk5_0,esk6_0)&(k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0&(esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.12/0.38  cnf(c_0_8, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_9, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_10, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k3_zfmisc_1(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_11, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_9]), c_0_9])).
% 0.12/0.38  fof(c_0_13, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (X1=esk6_0|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),X4)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.38  cnf(c_0_16, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_14, c_0_9])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|esk6_0=esk3_0|X1=k1_xboole_0), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_19, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (esk6_0=esk3_0|esk3_0=k1_xboole_0|X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.12/0.38  cnf(c_0_21, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (esk3_0=k1_xboole_0|esk6_0=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_20]), c_0_19]), c_0_17])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (X1=esk5_0|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)!=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.38  cnf(c_0_25, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_9]), c_0_9])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=esk1_0|esk5_0!=esk2_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk5_0=esk2_0), inference(er,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (X1=esk4_0|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_12])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0!=esk1_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.38  cnf(c_0_30, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.12/0.38  cnf(c_0_32, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_31]), c_0_32])])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_33]), c_0_32]), c_0_19])])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_34]), c_0_19]), c_0_19])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 36
% 0.12/0.38  # Proof object clause steps            : 27
% 0.12/0.38  # Proof object formula steps           : 9
% 0.12/0.38  # Proof object conjectures             : 21
% 0.12/0.38  # Proof object clause conjectures      : 18
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 8
% 0.12/0.38  # Proof object initial formulas used   : 4
% 0.12/0.38  # Proof object generating inferences   : 12
% 0.12/0.38  # Proof object simplifying inferences  : 23
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 4
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 10
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 9
% 0.12/0.38  # Processed clauses                    : 119
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 60
% 0.12/0.38  # ...remaining for further processing  : 59
% 0.12/0.38  # Other redundant clauses eliminated   : 5
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 10
% 0.12/0.38  # Backward-rewritten                   : 25
% 0.12/0.38  # Generated clauses                    : 510
% 0.12/0.38  # ...of the previous two non-trivial   : 514
% 0.12/0.38  # Contextual simplify-reflections      : 3
% 0.12/0.38  # Paramodulations                      : 484
% 0.12/0.38  # Factorizations                       : 8
% 0.12/0.38  # Equation resolutions                 : 18
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 13
% 0.12/0.38  #    Positive orientable unit clauses  : 3
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 10
% 0.12/0.38  # Current number of unprocessed clauses: 354
% 0.12/0.38  # ...number of literals in the above   : 2430
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 45
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 324
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 199
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 51
% 0.12/0.38  # Unit Clause-clause subsumption calls : 0
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 8646
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.036 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.041 s
% 0.12/0.38  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
