%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:52 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 267 expanded)
%              Number of clauses        :   21 ( 104 expanded)
%              Number of leaves         :    5 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 924 expanded)
%              Number of equality atoms :   61 ( 794 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                  & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                  & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_mcart_1])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14] :
      ( X11 = k1_xboole_0
      | X12 = k1_xboole_0
      | X13 = k1_xboole_0
      | ~ m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))
      | X14 = k3_mcart_1(k5_mcart_1(X11,X12,X13,X14),k6_mcart_1(X11,X12,X13,X14),k7_mcart_1(X11,X12,X13,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7] : k3_mcart_1(X5,X6,X7) = k4_tarski(k4_tarski(X5,X6),X7) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] : k3_zfmisc_1(X8,X9,X10) = k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0))
      | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(k1_mcart_1(esk4_0))
      | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( k1_mcart_1(k4_tarski(X15,X16)) = X15
      & k2_mcart_1(k4_tarski(X15,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_15,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0))
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(k1_mcart_1(esk4_0))
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(k1_mcart_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0))
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(k1_mcart_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_mcart_1(k1_mcart_1(esk4_0))) = k1_mcart_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_29]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.37  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t50_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.13/0.37  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.13/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4))))))), inference(assume_negation,[status(cth)],[t50_mcart_1])).
% 0.13/0.37  fof(c_0_6, plain, ![X11, X12, X13, X14]:(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|(~m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))|X14=k3_mcart_1(k5_mcart_1(X11,X12,X13,X14),k6_mcart_1(X11,X12,X13,X14),k7_mcart_1(X11,X12,X13,X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X5, X6, X7]:k3_mcart_1(X5,X6,X7)=k4_tarski(k4_tarski(X5,X6),X7), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.37  fof(c_0_8, plain, ![X8, X9, X10]:k3_zfmisc_1(X8,X9,X10)=k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, (((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&(m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_mcart_1(k1_mcart_1(esk4_0))|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_mcart_1(k1_mcart_1(esk4_0))|k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_mcart_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.37  cnf(c_0_10, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_11, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_14, plain, ![X15, X16]:(k1_mcart_1(k4_tarski(X15,X16))=X15&k2_mcart_1(k4_tarski(X15,X16))=X16), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.37  cnf(c_0_15, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_13, c_0_12])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0))=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k2_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_23, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_mcart_1(esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0))=k1_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_mcart_1(k1_mcart_1(esk4_0))|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_mcart_1(k1_mcart_1(esk4_0))|k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_mcart_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k2_mcart_1(k1_mcart_1(esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_mcart_1(k1_mcart_1(esk4_0))|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_mcart_1(k1_mcart_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22])])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_mcart_1(k1_mcart_1(esk4_0)))=k1_mcart_1(esk4_0)), inference(rw,[status(thm)],[c_0_25, c_0_27])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_mcart_1(k1_mcart_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_27])])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_29]), c_0_30]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 32
% 0.13/0.37  # Proof object clause steps            : 21
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 18
% 0.13/0.37  # Proof object clause conjectures      : 15
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 10
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 5
% 0.13/0.37  # Proof object simplifying inferences  : 13
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 10
% 0.13/0.37  # Removed in clause preprocessing      : 2
% 0.13/0.37  # Initial clauses in saturation        : 8
% 0.13/0.37  # Processed clauses                    : 25
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 25
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 5
% 0.13/0.37  # Generated clauses                    : 7
% 0.13/0.37  # ...of the previous two non-trivial   : 11
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 7
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
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
% 0.13/0.37  #    Positive orientable unit clauses  : 7
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 4
% 0.13/0.37  #    Non-unit-clauses                  : 1
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 15
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 7
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 3
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 738
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
