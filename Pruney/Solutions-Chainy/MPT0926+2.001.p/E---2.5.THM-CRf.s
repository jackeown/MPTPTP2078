%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:33 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 236 expanded)
%              Number of clauses        :   29 (  73 expanded)
%              Number of leaves         :    2 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 (2590 expanded)
%              Number of equality atoms :  116 (2235 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & X5 != k1_xboole_0
        & X6 != k1_xboole_0
        & X7 != k1_xboole_0
        & X8 != k1_xboole_0
        & ? [X9] :
            ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
            & ? [X10] :
                ( m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))
                & X9 = X10
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X9) = k8_mcart_1(X5,X6,X7,X8,X10)
                    & k9_mcart_1(X1,X2,X3,X4,X9) = k9_mcart_1(X5,X6,X7,X8,X10)
                    & k10_mcart_1(X1,X2,X3,X4,X9) = k10_mcart_1(X5,X6,X7,X8,X10)
                    & k11_mcart_1(X1,X2,X3,X4,X9) = k11_mcart_1(X5,X6,X7,X8,X10) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

fof(t61_mcart_1,axiom,(
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

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & X5 != k1_xboole_0
          & X6 != k1_xboole_0
          & X7 != k1_xboole_0
          & X8 != k1_xboole_0
          & ? [X9] :
              ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
              & ? [X10] :
                  ( m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))
                  & X9 = X10
                  & ~ ( k8_mcart_1(X1,X2,X3,X4,X9) = k8_mcart_1(X5,X6,X7,X8,X10)
                      & k9_mcart_1(X1,X2,X3,X4,X9) = k9_mcart_1(X5,X6,X7,X8,X10)
                      & k10_mcart_1(X1,X2,X3,X4,X9) = k10_mcart_1(X5,X6,X7,X8,X10)
                      & k11_mcart_1(X1,X2,X3,X4,X9) = k11_mcart_1(X5,X6,X7,X8,X10) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_mcart_1])).

fof(c_0_3,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & esk9_0 = esk10_0
    & ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
      | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
      | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
      | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( k8_mcart_1(X11,X12,X13,X14,X15) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X15)))
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( k9_mcart_1(X11,X12,X13,X14,X15) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X15)))
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( k10_mcart_1(X11,X12,X13,X14,X15) = k2_mcart_1(k1_mcart_1(X15))
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( k11_mcart_1(X11,X12,X13,X14,X15) = k2_mcart_1(X15)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_5,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_18,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_19,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_6]),c_0_6]),c_0_6]),c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k2_mcart_1(k1_mcart_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) = k2_mcart_1(k1_mcart_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k2_mcart_1(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) = k2_mcart_1(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_25,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_28,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) = k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:21:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.026 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t86_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:~(((((((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&X5!=k1_xboole_0)&X6!=k1_xboole_0)&X7!=k1_xboole_0)&X8!=k1_xboole_0)&?[X9]:(m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))&?[X10]:((m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))&X9=X10)&~((((k8_mcart_1(X1,X2,X3,X4,X9)=k8_mcart_1(X5,X6,X7,X8,X10)&k9_mcart_1(X1,X2,X3,X4,X9)=k9_mcart_1(X5,X6,X7,X8,X10))&k10_mcart_1(X1,X2,X3,X4,X9)=k10_mcart_1(X5,X6,X7,X8,X10))&k11_mcart_1(X1,X2,X3,X4,X9)=k11_mcart_1(X5,X6,X7,X8,X10))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_mcart_1)).
% 0.12/0.36  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.12/0.36  fof(c_0_2, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:~(((((((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&X5!=k1_xboole_0)&X6!=k1_xboole_0)&X7!=k1_xboole_0)&X8!=k1_xboole_0)&?[X9]:(m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))&?[X10]:((m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))&X9=X10)&~((((k8_mcart_1(X1,X2,X3,X4,X9)=k8_mcart_1(X5,X6,X7,X8,X10)&k9_mcart_1(X1,X2,X3,X4,X9)=k9_mcart_1(X5,X6,X7,X8,X10))&k10_mcart_1(X1,X2,X3,X4,X9)=k10_mcart_1(X5,X6,X7,X8,X10))&k11_mcart_1(X1,X2,X3,X4,X9)=k11_mcart_1(X5,X6,X7,X8,X10)))))))), inference(assume_negation,[status(cth)],[t86_mcart_1])).
% 0.12/0.36  fof(c_0_3, negated_conjecture, ((((((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&(m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&((m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&esk9_0=esk10_0)&(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).
% 0.12/0.36  fof(c_0_4, plain, ![X11, X12, X13, X14, X15]:((((k8_mcart_1(X11,X12,X13,X14,X15)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X15)))|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&(k9_mcart_1(X11,X12,X13,X14,X15)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X15)))|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)))&(k10_mcart_1(X11,X12,X13,X14,X15)=k2_mcart_1(k1_mcart_1(X15))|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)))&(k11_mcart_1(X11,X12,X13,X14,X15)=k2_mcart_1(X15)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.12/0.36  cnf(c_0_5, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_6, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_7, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_8, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[c_0_5, c_0_6])).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_11, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_18, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_19, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)|k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)|k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)|k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_6]), c_0_6]), c_0_6]), c_0_6])).
% 0.12/0.36  cnf(c_0_21, negated_conjecture, (k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)=k2_mcart_1(k1_mcart_1(esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)=k2_mcart_1(k1_mcart_1(esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)=k2_mcart_1(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)=k2_mcart_1(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.12/0.36  cnf(c_0_25, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)|k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24])])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.12/0.36  cnf(c_0_28, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)|k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)!=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.12/0.36  cnf(c_0_31, negated_conjecture, (k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_31]), c_0_32]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 34
% 0.12/0.36  # Proof object clause steps            : 29
% 0.12/0.36  # Proof object formula steps           : 5
% 0.12/0.36  # Proof object conjectures             : 28
% 0.12/0.36  # Proof object clause conjectures      : 25
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 16
% 0.12/0.36  # Proof object initial formulas used   : 2
% 0.12/0.36  # Proof object generating inferences   : 8
% 0.12/0.36  # Proof object simplifying inferences  : 47
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 2
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 16
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 16
% 0.12/0.36  # Processed clauses                    : 42
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 41
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 2
% 0.12/0.36  # Generated clauses                    : 8
% 0.12/0.36  # ...of the previous two non-trivial   : 10
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 8
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 23
% 0.12/0.36  #    Positive orientable unit clauses  : 10
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 9
% 0.12/0.36  #    Non-unit-clauses                  : 4
% 0.12/0.36  # Current number of unprocessed clauses: 0
% 0.12/0.36  # ...number of literals in the above   : 0
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 18
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 12
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 8
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 3
% 0.12/0.36  # BW rewrite match successes           : 2
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1202
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.028 s
% 0.12/0.36  # System time              : 0.002 s
% 0.12/0.36  # Total time               : 0.030 s
% 0.12/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
