%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:31 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 472 expanded)
%              Number of clauses        :   32 ( 151 expanded)
%              Number of leaves         :    4 ( 113 expanded)
%              Depth                    :   12
%              Number of atoms          :  277 (4619 expanded)
%              Number of equality atoms :  208 (2907 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t82_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
     => ( ! [X7] :
            ( m1_subset_1(X7,X1)
           => ! [X8] :
                ( m1_subset_1(X8,X2)
               => ! [X9] :
                    ( m1_subset_1(X9,X3)
                   => ! [X10] :
                        ( m1_subset_1(X10,X4)
                       => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                         => X5 = X10 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k11_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

fof(t79_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
     => ( ! [X7] :
            ( m1_subset_1(X7,X1)
           => ! [X8] :
                ( m1_subset_1(X8,X2)
               => ! [X9] :
                    ( m1_subset_1(X9,X3)
                   => ! [X10] :
                        ( m1_subset_1(X10,X4)
                       => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                         => X5 = X7 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k8_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

fof(t78_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ? [X6,X7,X8,X9] :
              ( X5 = k4_mcart_1(X6,X7,X8,X9)
              & ~ ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
                  & k9_mcart_1(X1,X2,X3,X4,X5) = X7
                  & k10_mcart_1(X1,X2,X3,X4,X5) = X8
                  & k11_mcart_1(X1,X2,X3,X4,X5) = X9 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

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

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
       => ( ! [X7] :
              ( m1_subset_1(X7,X1)
             => ! [X8] :
                  ( m1_subset_1(X8,X2)
                 => ! [X9] :
                      ( m1_subset_1(X9,X3)
                     => ! [X10] :
                          ( m1_subset_1(X10,X4)
                         => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                           => X5 = X10 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k11_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t82_mcart_1])).

fof(c_0_5,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( m1_subset_1(esk1_6(X25,X26,X27,X28,X29,X30),X25)
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k8_mcart_1(X25,X26,X27,X28,X30)
        | ~ m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)) )
      & ( m1_subset_1(esk2_6(X25,X26,X27,X28,X29,X30),X26)
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k8_mcart_1(X25,X26,X27,X28,X30)
        | ~ m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)) )
      & ( m1_subset_1(esk3_6(X25,X26,X27,X28,X29,X30),X27)
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k8_mcart_1(X25,X26,X27,X28,X30)
        | ~ m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)) )
      & ( m1_subset_1(esk4_6(X25,X26,X27,X28,X29,X30),X28)
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k8_mcart_1(X25,X26,X27,X28,X30)
        | ~ m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)) )
      & ( X30 = k4_mcart_1(esk1_6(X25,X26,X27,X28,X29,X30),esk2_6(X25,X26,X27,X28,X29,X30),esk3_6(X25,X26,X27,X28,X29,X30),esk4_6(X25,X26,X27,X28,X29,X30))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k8_mcart_1(X25,X26,X27,X28,X30)
        | ~ m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)) )
      & ( X29 != esk1_6(X25,X26,X27,X28,X29,X30)
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k8_mcart_1(X25,X26,X27,X28,X30)
        | ~ m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_mcart_1])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X41,X42,X43,X44] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X41,esk5_0)
        | ~ m1_subset_1(X42,esk6_0)
        | ~ m1_subset_1(X43,esk7_0)
        | ~ m1_subset_1(X44,esk8_0)
        | esk10_0 != k4_mcart_1(X41,X42,X43,X44)
        | esk9_0 = X44 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( esk9_0 = X4
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X4,esk8_0)
    | esk10_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( k8_mcart_1(X16,X17,X18,X19,X20) = X21
        | X20 != k4_mcart_1(X21,X22,X23,X24)
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)) )
      & ( k9_mcart_1(X16,X17,X18,X19,X20) = X22
        | X20 != k4_mcart_1(X21,X22,X23,X24)
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)) )
      & ( k10_mcart_1(X16,X17,X18,X19,X20) = X23
        | X20 != k4_mcart_1(X21,X22,X23,X24)
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)) )
      & ( k11_mcart_1(X16,X17,X18,X19,X20) = X24
        | X20 != k4_mcart_1(X21,X22,X23,X24)
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).

cnf(c_0_17,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X2
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X3,X4,X2) != esk10_0
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X4,esk7_0)
    | ~ m1_subset_1(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X9,X6)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( X1 = k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k8_mcart_1(X2,X3,X4,X5,X1)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_22,plain,(
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

cnf(c_0_23,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X3
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X4,X3) != esk10_0
    | ~ m1_subset_1(X3,esk8_0)
    | ~ m1_subset_1(X4,esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( k11_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X8
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) = esk10_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_28,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X3 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X4
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X4) != esk10_0
    | ~ m1_subset_1(X4,esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( k11_mcart_1(X1,X2,X3,X4,esk10_0) = esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X5,esk10_0)
    | X5 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = k2_mcart_1(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X3 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X4 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X4,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk9_0 != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = k2_mcart_1(esk10_0)
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_8]),c_0_32]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k2_mcart_1(esk10_0) != esk9_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( X1 = X2 ),
    inference(spm,[status(thm)],[c_0_38,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_12,c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.21/0.40  # and selection function SelectNegativeLiterals.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.028 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t82_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X10)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k11_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_mcart_1)).
% 0.21/0.40  fof(t79_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 0.21/0.40  fof(t78_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.21/0.40  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.21/0.40  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X10)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k11_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t82_mcart_1])).
% 0.21/0.40  fof(c_0_5, plain, ![X25, X26, X27, X28, X29, X30]:((m1_subset_1(esk1_6(X25,X26,X27,X28,X29,X30),X25)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((m1_subset_1(esk2_6(X25,X26,X27,X28,X29,X30),X26)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((m1_subset_1(esk3_6(X25,X26,X27,X28,X29,X30),X27)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((m1_subset_1(esk4_6(X25,X26,X27,X28,X29,X30),X28)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((X30=k4_mcart_1(esk1_6(X25,X26,X27,X28,X29,X30),esk2_6(X25,X26,X27,X28,X29,X30),esk3_6(X25,X26,X27,X28,X29,X30),esk4_6(X25,X26,X27,X28,X29,X30))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&(X29!=esk1_6(X25,X26,X27,X28,X29,X30)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_mcart_1])])])])).
% 0.21/0.40  fof(c_0_6, negated_conjecture, ![X41, X42, X43, X44]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X41,esk5_0)|(~m1_subset_1(X42,esk6_0)|(~m1_subset_1(X43,esk7_0)|(~m1_subset_1(X44,esk8_0)|(esk10_0!=k4_mcart_1(X41,X42,X43,X44)|esk9_0=X44)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.21/0.40  cnf(c_0_7, plain, (m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_9, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_10, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_11, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_12, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_13, negated_conjecture, (esk9_0=X4|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_14, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.21/0.40  cnf(c_0_15, plain, (m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  fof(c_0_16, plain, ![X16, X17, X18, X19, X20, X21, X22, X23, X24]:((((k8_mcart_1(X16,X17,X18,X19,X20)=X21|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)))&(k9_mcart_1(X16,X17,X18,X19,X20)=X22|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19))))&(k10_mcart_1(X16,X17,X18,X19,X20)=X23|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19))))&(k11_mcart_1(X16,X17,X18,X19,X20)=X24|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).
% 0.21/0.40  cnf(c_0_17, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X2|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X3,X4,X2)!=esk10_0|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X4,esk7_0)|~m1_subset_1(X3,esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.21/0.40  cnf(c_0_19, plain, (m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  cnf(c_0_20, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X9,X6)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_21, plain, (X1=k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X6=k8_mcart_1(X2,X3,X4,X5,X1)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  fof(c_0_22, plain, ![X11, X12, X13, X14, X15]:((((k8_mcart_1(X11,X12,X13,X14,X15)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X15)))|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&(k9_mcart_1(X11,X12,X13,X14,X15)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X15)))|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)))&(k10_mcart_1(X11,X12,X13,X14,X15)=k2_mcart_1(k1_mcart_1(X15))|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)))&(k11_mcart_1(X11,X12,X13,X14,X15)=k2_mcart_1(X15)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X3|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X4,X3)!=esk10_0|~m1_subset_1(X3,esk8_0)|~m1_subset_1(X4,esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.40  cnf(c_0_24, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.21/0.40  cnf(c_0_25, plain, (m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  cnf(c_0_26, plain, (k11_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X8|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))=esk10_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.21/0.40  cnf(c_0_28, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_29, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X3=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X4|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X4)!=esk10_0|~m1_subset_1(X4,esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (k11_mcart_1(X1,X2,X3,X4,esk10_0)=esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X5,esk10_0)|X5=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=k2_mcart_1(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X3=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X4=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X4,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))!=esk10_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (esk9_0!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=k2_mcart_1(esk10_0)|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_8]), c_0_32]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_33, c_0_27])).
% 0.21/0.40  cnf(c_0_37, negated_conjecture, (k2_mcart_1(esk10_0)!=esk9_0), inference(rw,[status(thm)],[c_0_34, c_0_32])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.21/0.40  cnf(c_0_39, negated_conjecture, (X1=X2), inference(spm,[status(thm)],[c_0_38, c_0_38])).
% 0.21/0.40  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_12, c_0_39]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 41
% 0.21/0.40  # Proof object clause steps            : 32
% 0.21/0.40  # Proof object formula steps           : 9
% 0.21/0.40  # Proof object conjectures             : 27
% 0.21/0.40  # Proof object clause conjectures      : 24
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 14
% 0.21/0.40  # Proof object initial formulas used   : 4
% 0.21/0.40  # Proof object generating inferences   : 15
% 0.21/0.40  # Proof object simplifying inferences  : 33
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 4
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 21
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 21
% 0.21/0.40  # Processed clauses                    : 218
% 0.21/0.40  # ...of these trivial                  : 2
% 0.21/0.40  # ...subsumed                          : 84
% 0.21/0.40  # ...remaining for further processing  : 132
% 0.21/0.40  # Other redundant clauses eliminated   : 4
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 15
% 0.21/0.40  # Backward-rewritten                   : 85
% 0.21/0.40  # Generated clauses                    : 340
% 0.21/0.40  # ...of the previous two non-trivial   : 393
% 0.21/0.40  # Contextual simplify-reflections      : 1
% 0.21/0.40  # Paramodulations                      : 330
% 0.21/0.40  # Factorizations                       : 1
% 0.21/0.40  # Equation resolutions                 : 4
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 2
% 0.21/0.40  #    Positive orientable unit clauses  : 1
% 0.21/0.40  #    Positive unorientable unit clauses: 1
% 0.21/0.40  #    Negative unit clauses             : 0
% 0.21/0.40  #    Non-unit-clauses                  : 0
% 0.21/0.40  # Current number of unprocessed clauses: 198
% 0.21/0.40  # ...number of literals in the above   : 989
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 126
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 1988
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 173
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 95
% 0.21/0.40  # Unit Clause-clause subsumption calls : 11
% 0.21/0.40  # Rewrite failures with RHS unbound    : 31
% 0.21/0.40  # BW rewrite match attempts            : 143
% 0.21/0.40  # BW rewrite match successes           : 135
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 13912
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.044 s
% 0.21/0.40  # System time              : 0.007 s
% 0.21/0.40  # Total time               : 0.051 s
% 0.21/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
