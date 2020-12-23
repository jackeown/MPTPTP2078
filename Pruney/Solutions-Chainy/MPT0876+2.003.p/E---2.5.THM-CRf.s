%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 509 expanded)
%              Number of clauses        :   33 ( 203 expanded)
%              Number of leaves         :    4 ( 123 expanded)
%              Depth                    :   18
%              Number of atoms          :  117 (2079 expanded)
%              Number of equality atoms :  116 (2078 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_mcart_1,conjecture,(
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

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_mcart_1])).

fof(c_0_5,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X13,X14,X15] : k3_zfmisc_1(X13,X14,X15) = k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | k2_zfmisc_1(X9,X10) != k2_zfmisc_1(X11,X12) )
      & ( X10 = X12
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | k2_zfmisc_1(X9,X10) != k2_zfmisc_1(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_8,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( X1 = esk6_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_20,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_23]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk4_0,esk5_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | X1 = esk4_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 != esk1_0
    | esk5_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_19])])).

cnf(c_0_29,negated_conjecture,
    ( esk5_0 = esk2_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_18]),c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk4_0 != esk1_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_33]),c_0_17]),c_0_18])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_18])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_35]),c_0_37]),c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_40]),c_0_17]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t36_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.13/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6)))), inference(assume_negation,[status(cth)],[t36_mcart_1])).
% 0.13/0.37  fof(c_0_5, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k3_zfmisc_1(esk4_0,esk5_0,esk6_0)&(((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&(esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X13, X14, X15]:k3_zfmisc_1(X13,X14,X15)=k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_7, plain, ![X9, X10, X11, X12]:((X9=X11|(X9=k1_xboole_0|X10=k1_xboole_0)|k2_zfmisc_1(X9,X10)!=k2_zfmisc_1(X11,X12))&(X10=X12|(X9=k1_xboole_0|X10=k1_xboole_0)|k2_zfmisc_1(X9,X10)!=k2_zfmisc_1(X11,X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.13/0.37  cnf(c_0_8, negated_conjecture, (k3_zfmisc_1(esk1_0,esk2_0,esk3_0)=k3_zfmisc_1(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_9, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.13/0.37  fof(c_0_12, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (X1=esk6_0|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_15, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk6_0=esk3_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (esk6_0=esk3_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.37  cnf(c_0_20, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk3_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_11, c_0_19])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(esk4_0,esk5_0)=X1|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k2_zfmisc_1(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_14])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k2_zfmisc_1(esk1_0,esk2_0)|k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (esk1_0!=esk4_0|esk2_0!=esk5_0|esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=X1|k2_zfmisc_1(esk1_0,esk2_0)!=k2_zfmisc_1(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_23]), c_0_15])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (X1=k2_zfmisc_1(esk4_0,esk5_0)|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|X1=esk4_0|X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (esk4_0!=esk1_0|esk5_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_19])])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (esk5_0=esk2_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k2_zfmisc_1(esk1_0,esk2_0)|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_14])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|esk4_0=esk1_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_27]), c_0_18]), c_0_17])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk4_0!=esk1_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk4_0=esk1_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_31]), c_0_32])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (esk4_0=esk1_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_33]), c_0_17]), c_0_18])).
% 0.13/0.37  cnf(c_0_36, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_18])).
% 0.13/0.37  cnf(c_0_38, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_35]), c_0_37]), c_0_38])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_40]), c_0_17]), c_0_18]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 42
% 0.13/0.37  # Proof object clause steps            : 33
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 30
% 0.13/0.37  # Proof object clause conjectures      : 27
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 10
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 17
% 0.13/0.37  # Proof object simplifying inferences  : 24
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 11
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 10
% 0.13/0.37  # Processed clauses                    : 96
% 0.13/0.37  # ...of these trivial                  : 4
% 0.13/0.37  # ...subsumed                          : 35
% 0.13/0.37  # ...remaining for further processing  : 57
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 12
% 0.13/0.37  # Backward-rewritten                   : 21
% 0.13/0.37  # Generated clauses                    : 150
% 0.13/0.37  # ...of the previous two non-trivial   : 149
% 0.13/0.37  # Contextual simplify-reflections      : 3
% 0.13/0.37  # Paramodulations                      : 133
% 0.13/0.37  # Factorizations                       : 6
% 0.13/0.37  # Equation resolutions                 : 11
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
% 0.13/0.37  # Current number of processed clauses  : 12
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 3
% 0.13/0.37  # Current number of unprocessed clauses: 32
% 0.13/0.37  # ...number of literals in the above   : 140
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 44
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 138
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 107
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 44
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 3
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2285
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
