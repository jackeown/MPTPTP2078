%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 108 expanded)
%              Number of clauses        :   25 (  42 expanded)
%              Number of leaves         :    3 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 573 expanded)
%              Number of equality atoms :  112 ( 494 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ? [X5,X6,X7] :
                ( X4 = k3_mcart_1(X5,X6,X7)
                & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                    & k6_mcart_1(X1,X2,X3,X4) = X6
                    & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(c_0_3,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( k5_mcart_1(X11,X12,X13,X14) = X15
        | X14 != k3_mcart_1(X15,X16,X17)
        | ~ m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( k6_mcart_1(X11,X12,X13,X14) = X16
        | X14 != k3_mcart_1(X15,X16,X17)
        | ~ m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( k7_mcart_1(X11,X12,X13,X14) = X17
        | X14 != k3_mcart_1(X15,X16,X17)
        | ~ m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_mcart_1])])])])).

fof(c_0_4,plain,(
    ! [X8,X9,X10] : k3_zfmisc_1(X8,X9,X10) = k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_5,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X5,X6,X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,negated_conjecture,(
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

cnf(c_0_8,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k3_mcart_1(X5,X6,X7)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_5,c_0_6])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 = k3_mcart_1(esk5_0,esk6_0,esk7_0)
    & ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0
      | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0
      | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk7_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X5,X7)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( esk4_0 = k3_mcart_1(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k3_mcart_1(X6,X5,X7)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_6])).

cnf(c_0_15,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X7,X5)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk4_0) = esk5_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X5
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k3_mcart_1(X6,X7,X5)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk5_0
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk4_0) = esk6_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_26,plain,
    ( k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk6_0
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk4_0) = esk7_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_30]),c_0_18]),c_0_19]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:46:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t47_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_mcart_1)).
% 0.19/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.37  fof(t68_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 0.19/0.37  fof(c_0_3, plain, ![X11, X12, X13, X14, X15, X16, X17]:(((k5_mcart_1(X11,X12,X13,X14)=X15|X14!=k3_mcart_1(X15,X16,X17)|~m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0))&(k6_mcart_1(X11,X12,X13,X14)=X16|X14!=k3_mcart_1(X15,X16,X17)|~m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0)))&(k7_mcart_1(X11,X12,X13,X14)=X17|X14!=k3_mcart_1(X15,X16,X17)|~m1_subset_1(X14,k3_zfmisc_1(X11,X12,X13))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_mcart_1])])])])).
% 0.19/0.37  fof(c_0_4, plain, ![X8, X9, X10]:k3_zfmisc_1(X8,X9,X10)=k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.37  cnf(c_0_5, plain, (k5_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X5,X6,X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.19/0.37  cnf(c_0_6, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7))))))), inference(assume_negation,[status(cth)],[t68_mcart_1])).
% 0.19/0.37  cnf(c_0_8, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=X5|X4!=k3_mcart_1(X5,X6,X7)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_5, c_0_6])).
% 0.19/0.37  fof(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&(((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&(esk4_0=k3_mcart_1(esk5_0,esk6_0,esk7_0)&(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk5_0|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0|k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.37  cnf(c_0_10, plain, (k6_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X5,X7)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.19/0.37  cnf(c_0_11, plain, (k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (esk4_0=k3_mcart_1(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=X5|X4!=k3_mcart_1(X6,X5,X7)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_10, c_0_6])).
% 0.19/0.37  cnf(c_0_15, plain, (k7_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X7,X5)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (k5_mcart_1(X1,X2,X3,esk4_0)=esk5_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_13, c_0_6])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_21, plain, (k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X5|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=X5|X4!=k3_mcart_1(X6,X7,X5)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_15, c_0_6])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk5_0|k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0|k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (k6_mcart_1(X1,X2,X3,esk4_0)=esk6_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_21, c_0_12])).
% 0.19/0.37  cnf(c_0_26, plain, (k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X6|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk6_0|k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (k7_mcart_1(X1,X2,X3,esk4_0)=esk7_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk4_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_26, c_0_12])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_17]), c_0_30]), c_0_18]), c_0_19]), c_0_20]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 32
% 0.19/0.37  # Proof object clause steps            : 25
% 0.19/0.37  # Proof object formula steps           : 7
% 0.19/0.37  # Proof object conjectures             : 18
% 0.19/0.37  # Proof object clause conjectures      : 15
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 10
% 0.19/0.37  # Proof object initial formulas used   : 3
% 0.19/0.37  # Proof object generating inferences   : 6
% 0.19/0.37  # Proof object simplifying inferences  : 21
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 3
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 10
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 9
% 0.19/0.37  # Processed clauses                    : 28
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 28
% 0.19/0.37  # Other redundant clauses eliminated   : 3
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 9
% 0.19/0.37  # ...of the previous two non-trivial   : 10
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 6
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 3
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 14
% 0.19/0.37  #    Positive orientable unit clauses  : 4
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 6
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 12
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 2
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 898
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.028 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
