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
% DateTime   : Thu Dec  3 11:00:08 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 149 expanded)
%              Number of clauses        :   30 (  60 expanded)
%              Number of leaves         :    5 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 607 expanded)
%              Number of equality atoms :   97 ( 531 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ? [X5,X6,X7] :
              ( X4 = k3_mcart_1(X5,X6,X7)
              & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                  & k6_mcart_1(X1,X2,X3,X4) = X6
                  & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t50_mcart_1,axiom,(
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

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
       => ~ ( X1 != k1_xboole_0
            & X2 != k1_xboole_0
            & X3 != k1_xboole_0
            & ? [X5,X6,X7] :
                ( X4 = k3_mcart_1(X5,X6,X7)
                & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                    & k6_mcart_1(X1,X2,X3,X4) = X6
                    & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_mcart_1])).

fof(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 = k3_mcart_1(esk5_0,esk6_0,esk7_0)
    & ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0
      | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0
      | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk7_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] : k3_mcart_1(X8,X9,X10) = k4_tarski(k4_tarski(X8,X9),X10) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,plain,(
    ! [X14,X15,X16,X17] :
      ( ( k5_mcart_1(X14,X15,X16,X17) = k1_mcart_1(k1_mcart_1(X17))
        | ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( k6_mcart_1(X14,X15,X16,X17) = k2_mcart_1(k1_mcart_1(X17))
        | ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( k7_mcart_1(X14,X15,X16,X17) = k2_mcart_1(X17)
        | ~ m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] : k3_zfmisc_1(X11,X12,X13) = k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( k1_mcart_1(k4_tarski(X18,X19)) = X18
      & k2_mcart_1(k4_tarski(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_11,negated_conjecture,
    ( esk4_0 = k3_mcart_1(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 = k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( k4_tarski(esk5_0,esk6_0) = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),esk7_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_28,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0
    | k2_mcart_1(esk4_0) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k2_mcart_1(esk4_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk4_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

cnf(c_0_33,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_32])).

cnf(c_0_36,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(k1_mcart_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk4_0)) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.21/0.39  # and selection function SelectCQIArNpEqFirst.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.040 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t68_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_mcart_1)).
% 0.21/0.39  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.39  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.21/0.39  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.39  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.39  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7))))))), inference(assume_negation,[status(cth)],[t68_mcart_1])).
% 0.21/0.39  fof(c_0_6, negated_conjecture, (m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&(((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&(esk4_0=k3_mcart_1(esk5_0,esk6_0,esk7_0)&(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk5_0|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0|k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.21/0.39  fof(c_0_7, plain, ![X8, X9, X10]:k3_mcart_1(X8,X9,X10)=k4_tarski(k4_tarski(X8,X9),X10), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.39  fof(c_0_8, plain, ![X14, X15, X16, X17]:(((k5_mcart_1(X14,X15,X16,X17)=k1_mcart_1(k1_mcart_1(X17))|~m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))|(X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0))&(k6_mcart_1(X14,X15,X16,X17)=k2_mcart_1(k1_mcart_1(X17))|~m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))|(X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0)))&(k7_mcart_1(X14,X15,X16,X17)=k2_mcart_1(X17)|~m1_subset_1(X17,k3_zfmisc_1(X14,X15,X16))|(X14=k1_xboole_0|X15=k1_xboole_0|X16=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.21/0.39  fof(c_0_9, plain, ![X11, X12, X13]:k3_zfmisc_1(X11,X12,X13)=k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.39  fof(c_0_10, plain, ![X18, X19]:(k1_mcart_1(k4_tarski(X18,X19))=X18&k2_mcart_1(k4_tarski(X18,X19))=X19), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.39  cnf(c_0_11, negated_conjecture, (esk4_0=k3_mcart_1(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_12, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_13, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_14, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_16, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (esk4_0=k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.39  cnf(c_0_18, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (k4_tarski(esk5_0,esk6_0)=k1_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk5_0|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0|k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k2_mcart_1(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.21/0.39  cnf(c_0_26, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),esk7_0)=esk4_0), inference(rw,[status(thm)],[c_0_17, c_0_23])).
% 0.21/0.39  cnf(c_0_28, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk5_0|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0|k2_mcart_1(esk4_0)!=esk7_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (k2_mcart_1(esk4_0)=esk7_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.39  cnf(c_0_31, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_28, c_0_14])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk4_0))=esk5_0), inference(spm,[status(thm)],[c_0_16, c_0_23])).
% 0.21/0.39  cnf(c_0_33, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk5_0|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk5_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_32])).
% 0.21/0.39  cnf(c_0_36, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_33, c_0_14])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k2_mcart_1(k1_mcart_1(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk4_0))!=esk6_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_39]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 41
% 0.21/0.39  # Proof object clause steps            : 30
% 0.21/0.39  # Proof object formula steps           : 11
% 0.21/0.39  # Proof object conjectures             : 23
% 0.21/0.39  # Proof object clause conjectures      : 20
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 13
% 0.21/0.39  # Proof object initial formulas used   : 5
% 0.21/0.39  # Proof object generating inferences   : 7
% 0.21/0.39  # Proof object simplifying inferences  : 23
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 5
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 13
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 11
% 0.21/0.39  # Processed clauses                    : 35
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 34
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 6
% 0.21/0.39  # Generated clauses                    : 7
% 0.21/0.39  # ...of the previous two non-trivial   : 13
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 7
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 0
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 17
% 0.21/0.39  #    Positive orientable unit clauses  : 10
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 4
% 0.21/0.39  #    Non-unit-clauses                  : 3
% 0.21/0.39  # Current number of unprocessed clauses: 0
% 0.21/0.39  # ...number of literals in the above   : 0
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 19
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 2
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.39  # Unit Clause-clause subsumption calls : 0
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 5
% 0.21/0.39  # BW rewrite match successes           : 5
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 916
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.042 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.046 s
% 0.21/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
