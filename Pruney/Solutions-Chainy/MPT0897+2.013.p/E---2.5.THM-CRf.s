%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 270 expanded)
%              Number of clauses        :   33 ( 113 expanded)
%              Number of leaves         :    3 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  185 (1549 expanded)
%              Number of equality atoms :  184 (1548 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(t56_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( X13 = X17
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X14 = X18
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X15 = X19
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) )
      & ( X16 = X20
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | k4_zfmisc_1(X13,X14,X15,X16) != k4_zfmisc_1(X17,X18,X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X5,X1) != k4_zfmisc_1(X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) != k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk8_0 = esk4_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_zfmisc_1(k1_xboole_0,X1,X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_15,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X1,X5) != k4_zfmisc_1(X6,X7,X2,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk4_0) = k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X3,X1,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_19,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X1,X3,X4,X5) != k4_zfmisc_1(X2,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_20]),c_0_12]),c_0_13])).

cnf(c_0_24,plain,
    ( k4_zfmisc_1(X1,X2,X3,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | k4_zfmisc_1(X3,X1,X4,X5) != k4_zfmisc_1(X6,X2,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( esk5_0 = esk1_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_23]),c_0_24]),c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = X1
    | k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k4_zfmisc_1(X2,X1,X3,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_14]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_31]),c_0_12]),c_0_13])).

cnf(c_0_33,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_32]),c_0_24]),c_0_13])).

cnf(c_0_35,plain,
    ( k4_zfmisc_1(X1,X2,k1_xboole_0,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_36,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_34]),c_0_35]),c_0_13])).

cnf(c_0_38,plain,
    ( k4_zfmisc_1(X1,k1_xboole_0,X2,X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_37]),c_0_38]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:24:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.12/0.38  fof(t56_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 0.12/0.38  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.12/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.12/0.38  fof(c_0_4, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((X13=X17|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20))&(X14=X18|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20)))&(X15=X19|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20)))&(X16=X20|(X13=k1_xboole_0|X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)|k4_zfmisc_1(X13,X14,X15,X16)!=k4_zfmisc_1(X17,X18,X19,X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_mcart_1])])])).
% 0.12/0.38  fof(c_0_5, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.38  cnf(c_0_6, plain, (X1=X2|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X1=k1_xboole_0|k4_zfmisc_1(X3,X4,X5,X1)!=k4_zfmisc_1(X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_7, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  fof(c_0_8, plain, ![X9, X10, X11, X12]:((X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)!=k1_xboole_0)&((((X9!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0)&(X10!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0))&(X11!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0))&(X12!=k1_xboole_0|k4_zfmisc_1(X9,X10,X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.12/0.38  cnf(c_0_9, negated_conjecture, (esk8_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=X1|k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k4_zfmisc_1(X2,X3,X4,X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.12/0.38  cnf(c_0_10, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_11, negated_conjecture, (esk8_0=esk4_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_12, plain, (k4_zfmisc_1(k1_xboole_0,X1,X2,X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=esk4_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_11]), c_0_12]), c_0_13])).
% 0.12/0.38  cnf(c_0_15, plain, (X1=X2|X3=k1_xboole_0|X4=k1_xboole_0|X1=k1_xboole_0|X5=k1_xboole_0|k4_zfmisc_1(X3,X4,X1,X5)!=k4_zfmisc_1(X6,X7,X2,X8)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk4_0)=k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_7, c_0_14])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(ef,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=X1|k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k4_zfmisc_1(X2,X3,X1,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.12/0.38  cnf(c_0_19, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|k4_zfmisc_1(X1,X3,X4,X5)!=k4_zfmisc_1(X2,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (esk7_0=esk3_0|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(er,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_21, plain, (k4_zfmisc_1(X2,X3,X4,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (esk8_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk5_0=X1|k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k4_zfmisc_1(X1,X2,X3,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_16]), c_0_17])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_20]), c_0_12]), c_0_13])).
% 0.12/0.38  cnf(c_0_24, plain, (k4_zfmisc_1(X1,X2,X3,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_25, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|k4_zfmisc_1(X3,X1,X4,X5)!=k4_zfmisc_1(X6,X2,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (esk5_0=esk1_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (esk7_0=esk3_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_23]), c_0_24]), c_0_13])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=X1|k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k4_zfmisc_1(X2,X1,X3,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_16]), c_0_17])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (esk8_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0!=esk2_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_14]), c_0_28])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_31]), c_0_12]), c_0_13])).
% 0.12/0.38  cnf(c_0_33, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_32]), c_0_24]), c_0_13])).
% 0.12/0.38  cnf(c_0_35, plain, (k4_zfmisc_1(X1,X2,k1_xboole_0,X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.12/0.38  cnf(c_0_36, plain, (k4_zfmisc_1(X2,X1,X3,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_34]), c_0_35]), c_0_13])).
% 0.12/0.38  cnf(c_0_38, plain, (k4_zfmisc_1(X1,k1_xboole_0,X2,X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_37]), c_0_38]), c_0_13]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 40
% 0.12/0.38  # Proof object clause steps            : 33
% 0.12/0.38  # Proof object formula steps           : 7
% 0.12/0.38  # Proof object conjectures             : 24
% 0.12/0.38  # Proof object clause conjectures      : 21
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 11
% 0.12/0.38  # Proof object initial formulas used   : 3
% 0.12/0.38  # Proof object generating inferences   : 17
% 0.12/0.38  # Proof object simplifying inferences  : 25
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 3
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 12
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 12
% 0.12/0.38  # Processed clauses                    : 112
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 54
% 0.12/0.38  # ...remaining for further processing  : 58
% 0.12/0.38  # Other redundant clauses eliminated   : 4
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 23
% 0.12/0.38  # Backward-rewritten                   : 4
% 0.12/0.38  # Generated clauses                    : 190
% 0.12/0.38  # ...of the previous two non-trivial   : 185
% 0.12/0.38  # Contextual simplify-reflections      : 8
% 0.12/0.38  # Paramodulations                      : 172
% 0.12/0.38  # Factorizations                       : 3
% 0.12/0.38  # Equation resolutions                 : 15
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
% 0.12/0.38  # Current number of processed clauses  : 15
% 0.12/0.38  #    Positive orientable unit clauses  : 5
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 9
% 0.12/0.38  # Current number of unprocessed clauses: 93
% 0.12/0.38  # ...number of literals in the above   : 698
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 39
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 421
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 251
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 61
% 0.12/0.38  # Unit Clause-clause subsumption calls : 0
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 11
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4469
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.035 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.039 s
% 0.12/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
