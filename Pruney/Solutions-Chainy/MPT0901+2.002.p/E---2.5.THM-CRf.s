%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:04 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 703 expanded)
%              Number of clauses        :   28 ( 275 expanded)
%              Number of leaves         :    6 ( 176 expanded)
%              Depth                    :   14
%              Number of atoms          :   93 (2883 expanded)
%              Number of equality atoms :   83 (2564 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t61_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12] : k4_mcart_1(X9,X10,X11,X12) = k4_tarski(k3_mcart_1(X9,X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] : k3_mcart_1(X6,X7,X8) = k4_tarski(k4_tarski(X6,X7),X8) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ~ ! [X5] :
                ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
               => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                  & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                  & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                  & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_mcart_1])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( X17 = k1_xboole_0
      | X18 = k1_xboole_0
      | X19 = k1_xboole_0
      | X20 = k1_xboole_0
      | ~ m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))
      | X21 = k4_mcart_1(k8_mcart_1(X17,X18,X19,X20,X21),k9_mcart_1(X17,X18,X19,X20,X21),k10_mcart_1(X17,X18,X19,X20,X21),k11_mcart_1(X17,X18,X19,X20,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_10,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16] : k4_zfmisc_1(X13,X14,X15,X16) = k2_zfmisc_1(k3_zfmisc_1(X13,X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_13,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
      | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
      | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(esk5_0))
      | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( k1_mcart_1(k4_tarski(X22,X23)) = X22
      & k2_mcart_1(k4_tarski(X22,X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_19,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k2_mcart_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k2_mcart_1(esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = k1_mcart_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k2_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k2_mcart_1(k1_mcart_1(esk5_0))) = k1_mcart_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(esk5_0))
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = k1_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_27])])).

cnf(c_0_36,negated_conjecture,
    ( k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))) = k1_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:26:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.12/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.12/0.37  fof(t61_mcart_1, conjecture, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.12/0.37  fof(t60_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 0.12/0.37  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.12/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.37  fof(c_0_6, plain, ![X9, X10, X11, X12]:k4_mcart_1(X9,X10,X11,X12)=k4_tarski(k3_mcart_1(X9,X10,X11),X12), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.12/0.37  fof(c_0_7, plain, ![X6, X7, X8]:k3_mcart_1(X6,X7,X8)=k4_tarski(k4_tarski(X6,X7),X8), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5))))))), inference(assume_negation,[status(cth)],[t61_mcart_1])).
% 0.12/0.37  fof(c_0_9, plain, ![X17, X18, X19, X20, X21]:(X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0|X20=k1_xboole_0|(~m1_subset_1(X21,k4_zfmisc_1(X17,X18,X19,X20))|X21=k4_mcart_1(k8_mcart_1(X17,X18,X19,X20,X21),k9_mcart_1(X17,X18,X19,X20,X21),k10_mcart_1(X17,X18,X19,X20,X21),k11_mcart_1(X17,X18,X19,X20,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).
% 0.12/0.37  cnf(c_0_10, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_11, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  fof(c_0_12, plain, ![X13, X14, X15, X16]:k4_zfmisc_1(X13,X14,X15,X16)=k2_zfmisc_1(k3_zfmisc_1(X13,X14,X15),X16), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.12/0.37  fof(c_0_13, negated_conjecture, ((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&(m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(k1_mcart_1(esk5_0))|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.37  cnf(c_0_14, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_15, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  cnf(c_0_16, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_18, plain, ![X22, X23]:(k1_mcart_1(k4_tarski(X22,X23))=X22&k2_mcart_1(k4_tarski(X22,X23))=X23), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.37  cnf(c_0_19, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_25, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=k2_mcart_1(esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_28, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k2_mcart_1(esk5_0))=esk5_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))=k1_mcart_1(esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=k2_mcart_1(k1_mcart_1(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_30])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k2_mcart_1(k1_mcart_1(esk5_0)))=k1_mcart_1(esk5_0)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(k1_mcart_1(esk5_0))|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))=k1_mcart_1(k1_mcart_1(esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_32])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(k1_mcart_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_27])])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))), inference(spm,[status(thm)],[c_0_25, c_0_34])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_31])])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))))=k1_mcart_1(k1_mcart_1(esk5_0))), inference(rw,[status(thm)],[c_0_34, c_0_36])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_36])])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_39]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 41
% 0.12/0.37  # Proof object clause steps            : 28
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 23
% 0.12/0.37  # Proof object clause conjectures      : 20
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 12
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 18
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 12
% 0.12/0.37  # Removed in clause preprocessing      : 3
% 0.12/0.37  # Initial clauses in saturation        : 9
% 0.12/0.37  # Processed clauses                    : 32
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 32
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 8
% 0.12/0.37  # Generated clauses                    : 10
% 0.12/0.37  # ...of the previous two non-trivial   : 17
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 10
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 15
% 0.12/0.37  #    Positive orientable unit clauses  : 9
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 5
% 0.12/0.37  #    Non-unit-clauses                  : 1
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 20
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 5
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1058
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.026 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
