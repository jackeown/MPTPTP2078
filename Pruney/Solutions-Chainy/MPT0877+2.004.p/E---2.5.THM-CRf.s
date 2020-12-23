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
% DateTime   : Thu Dec  3 10:59:39 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 176 expanded)
%              Number of clauses        :   25 (  74 expanded)
%              Number of leaves         :    3 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 808 expanded)
%              Number of equality atoms :  122 ( 807 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_mcart_1])).

fof(c_0_4,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( X10 = X13
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) )
      & ( X11 = X14
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) )
      & ( X12 = X15
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k3_zfmisc_1(X10,X11,X12) != k3_zfmisc_1(X13,X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0)
    & k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ( X7 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) != k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk6_0 = esk3_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_15,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( k3_zfmisc_1(esk4_0,esk5_0,esk3_0) = k3_zfmisc_1(esk1_0,esk2_0,esk3_0)
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X1,X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_19,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = esk1_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk5_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])).

cnf(c_0_25,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_24]),c_0_12]),c_0_13])).

cnf(c_0_27,plain,
    ( k3_zfmisc_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_26]),c_0_27]),c_0_13])).

cnf(c_0_30,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_29]),c_0_30]),c_0_13]),
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
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t37_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.14/0.37  fof(t36_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.14/0.37  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.14/0.37  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6)))), inference(assume_negation,[status(cth)],[t37_mcart_1])).
% 0.14/0.37  fof(c_0_4, plain, ![X10, X11, X12, X13, X14, X15]:(((X10=X13|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0)|k3_zfmisc_1(X10,X11,X12)!=k3_zfmisc_1(X13,X14,X15))&(X11=X14|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0)|k3_zfmisc_1(X10,X11,X12)!=k3_zfmisc_1(X13,X14,X15)))&(X12=X15|(X10=k1_xboole_0|X11=k1_xboole_0|X12=k1_xboole_0)|k3_zfmisc_1(X10,X11,X12)!=k3_zfmisc_1(X13,X14,X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).
% 0.14/0.37  fof(c_0_5, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k3_zfmisc_1(esk4_0,esk5_0,esk6_0)&(k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0&(esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.14/0.37  cnf(c_0_6, plain, (X1=X2|X3=k1_xboole_0|X4=k1_xboole_0|X1=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.37  cnf(c_0_7, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k3_zfmisc_1(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  fof(c_0_8, plain, ![X7, X8, X9]:((X7=k1_xboole_0|X8=k1_xboole_0|X9=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)!=k1_xboole_0)&(((X7!=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)=k1_xboole_0)&(X8!=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)=k1_xboole_0))&(X9!=k1_xboole_0|k3_zfmisc_1(X7,X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.14/0.37  cnf(c_0_9, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=X1|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k3_zfmisc_1(X2,X3,X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.14/0.37  cnf(c_0_10, plain, (k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_11, negated_conjecture, (esk6_0=esk3_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_12, plain, (k3_zfmisc_1(k1_xboole_0,X1,X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_11]), c_0_12]), c_0_13])).
% 0.14/0.37  cnf(c_0_15, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (k3_zfmisc_1(esk4_0,esk5_0,esk3_0)=k3_zfmisc_1(esk1_0,esk2_0,esk3_0)|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_7, c_0_14])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(ef,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=X1|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k3_zfmisc_1(X1,X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.14/0.37  cnf(c_0_19, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (esk4_0=esk1_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(er,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=X1|k3_zfmisc_1(esk1_0,esk2_0,esk3_0)!=k3_zfmisc_1(X2,X1,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_16]), c_0_17])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk5_0!=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_14])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23])).
% 0.14/0.37  cnf(c_0_25, plain, (k3_zfmisc_1(X2,X3,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_24]), c_0_12]), c_0_13])).
% 0.14/0.37  cnf(c_0_27, plain, (k3_zfmisc_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_28, plain, (k3_zfmisc_1(X2,X1,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_26]), c_0_27]), c_0_13])).
% 0.14/0.37  cnf(c_0_30, plain, (k3_zfmisc_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_28])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_29]), c_0_30]), c_0_13]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 32
% 0.14/0.37  # Proof object clause steps            : 25
% 0.14/0.37  # Proof object formula steps           : 7
% 0.14/0.37  # Proof object conjectures             : 19
% 0.14/0.37  # Proof object clause conjectures      : 16
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 9
% 0.14/0.37  # Proof object initial formulas used   : 3
% 0.14/0.37  # Proof object generating inferences   : 12
% 0.14/0.37  # Proof object simplifying inferences  : 16
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 3
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 10
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 10
% 0.14/0.37  # Processed clauses                    : 68
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 26
% 0.14/0.37  # ...remaining for further processing  : 42
% 0.14/0.37  # Other redundant clauses eliminated   : 3
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 13
% 0.14/0.37  # Backward-rewritten                   : 5
% 0.14/0.37  # Generated clauses                    : 99
% 0.14/0.37  # ...of the previous two non-trivial   : 97
% 0.14/0.37  # Contextual simplify-reflections      : 4
% 0.14/0.37  # Paramodulations                      : 87
% 0.14/0.37  # Factorizations                       : 2
% 0.14/0.37  # Equation resolutions                 : 10
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 11
% 0.14/0.37  #    Positive orientable unit clauses  : 4
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 6
% 0.14/0.37  # Current number of unprocessed clauses: 47
% 0.14/0.37  # ...number of literals in the above   : 300
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 28
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 128
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 100
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 32
% 0.14/0.37  # Unit Clause-clause subsumption calls : 0
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 5
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 2054
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.029 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.033 s
% 0.14/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
