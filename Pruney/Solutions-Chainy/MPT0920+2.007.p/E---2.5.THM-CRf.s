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
% DateTime   : Thu Dec  3 11:00:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 511 expanded)
%              Number of clauses        :   38 ( 186 expanded)
%              Number of leaves         :    5 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  290 (3948 expanded)
%              Number of equality atoms :  212 (2520 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_mcart_1,conjecture,(
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
                         => X5 = X8 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k9_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

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

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

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

fof(c_0_5,negated_conjecture,(
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
                           => X5 = X8 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k9_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_mcart_1])).

fof(c_0_6,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( m1_subset_1(esk1_6(X28,X29,X30,X31,X32,X33),X28)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k8_mcart_1(X28,X29,X30,X31,X33)
        | ~ m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( m1_subset_1(esk2_6(X28,X29,X30,X31,X32,X33),X29)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k8_mcart_1(X28,X29,X30,X31,X33)
        | ~ m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( m1_subset_1(esk3_6(X28,X29,X30,X31,X32,X33),X30)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k8_mcart_1(X28,X29,X30,X31,X33)
        | ~ m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( m1_subset_1(esk4_6(X28,X29,X30,X31,X32,X33),X31)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k8_mcart_1(X28,X29,X30,X31,X33)
        | ~ m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( X33 = k4_mcart_1(esk1_6(X28,X29,X30,X31,X32,X33),esk2_6(X28,X29,X30,X31,X32,X33),esk3_6(X28,X29,X30,X31,X32,X33),esk4_6(X28,X29,X30,X31,X32,X33))
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k8_mcart_1(X28,X29,X30,X31,X33)
        | ~ m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( X32 != esk1_6(X28,X29,X30,X31,X32,X33)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k8_mcart_1(X28,X29,X30,X31,X33)
        | ~ m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_mcart_1])])])])).

fof(c_0_7,plain,(
    ! [X15,X16,X17,X18] : k4_zfmisc_1(X15,X16,X17,X18) = k2_zfmisc_1(k3_zfmisc_1(X15,X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_8,negated_conjecture,(
    ! [X44,X45,X46,X47] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X44,esk5_0)
        | ~ m1_subset_1(X45,esk6_0)
        | ~ m1_subset_1(X46,esk7_0)
        | ~ m1_subset_1(X47,esk8_0)
        | esk10_0 != k4_mcart_1(X44,X45,X46,X47)
        | esk9_0 = X45 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14] : k4_mcart_1(X11,X12,X13,X14) = k4_tarski(k3_mcart_1(X11,X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk9_0 = X2
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X4,esk8_0)
    | esk10_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( esk9_0 = X2
    | esk10_0 != k4_tarski(k3_mcart_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X4,esk8_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( k8_mcart_1(X19,X20,X21,X22,X23) = X24
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22)) )
      & ( k9_mcart_1(X19,X20,X21,X22,X23) = X25
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22)) )
      & ( k10_mcart_1(X19,X20,X21,X22,X23) = X26
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22)) )
      & ( k11_mcart_1(X19,X20,X21,X22,X23) = X27
        | X23 != k4_mcart_1(X24,X25,X26,X27)
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X2
    | k4_tarski(k3_mcart_1(X3,X2,X4),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) != esk10_0
    | ~ m1_subset_1(X4,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_29,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X6,X8,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k8_mcart_1(X2,X3,X4,X5,X1)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X3
    | k4_tarski(k3_mcart_1(X4,X3,esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0)) != esk10_0
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X4,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_35,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_11])).

cnf(c_0_36,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k3_mcart_1(X7,X6,X8),X9)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_14]),c_0_11])).

cnf(c_0_37,plain,
    ( X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X6 = k8_mcart_1(X2,X3,X4,X5,X1)
    | X1 = k4_tarski(k3_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1)),esk4_6(X2,X3,X4,X5,X6,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_14]),c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X3 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k4_tarski(k3_mcart_1(X4,esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0)) != esk10_0
    | ~ m1_subset_1(X4,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_40,plain,
    ( k9_mcart_1(X1,X2,X3,X4,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X6
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k4_tarski(k3_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) = esk10_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X3 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X4 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k4_tarski(k3_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X4,esk10_0)) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k9_mcart_1(X1,X2,X3,X4,esk10_0) = esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X5,esk10_0)
    | X5 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( esk9_0 != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_RG_S070I
% 0.14/0.38  # and selection function SelectVGNonCR.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t80_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X8)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k9_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 0.14/0.38  fof(t79_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 0.14/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.14/0.38  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.14/0.38  fof(t78_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X8)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k9_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t80_mcart_1])).
% 0.14/0.38  fof(c_0_6, plain, ![X28, X29, X30, X31, X32, X33]:((m1_subset_1(esk1_6(X28,X29,X30,X31,X32,X33),X28)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k8_mcart_1(X28,X29,X30,X31,X33))|~m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)))&((m1_subset_1(esk2_6(X28,X29,X30,X31,X32,X33),X29)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k8_mcart_1(X28,X29,X30,X31,X33))|~m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)))&((m1_subset_1(esk3_6(X28,X29,X30,X31,X32,X33),X30)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k8_mcart_1(X28,X29,X30,X31,X33))|~m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)))&((m1_subset_1(esk4_6(X28,X29,X30,X31,X32,X33),X31)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k8_mcart_1(X28,X29,X30,X31,X33))|~m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)))&((X33=k4_mcart_1(esk1_6(X28,X29,X30,X31,X32,X33),esk2_6(X28,X29,X30,X31,X32,X33),esk3_6(X28,X29,X30,X31,X32,X33),esk4_6(X28,X29,X30,X31,X32,X33))|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k8_mcart_1(X28,X29,X30,X31,X33))|~m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)))&(X32!=esk1_6(X28,X29,X30,X31,X32,X33)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k8_mcart_1(X28,X29,X30,X31,X33))|~m1_subset_1(X33,k4_zfmisc_1(X28,X29,X30,X31)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_mcart_1])])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X15, X16, X17, X18]:k4_zfmisc_1(X15,X16,X17,X18)=k2_zfmisc_1(k3_zfmisc_1(X15,X16,X17),X18), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ![X44, X45, X46, X47]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X44,esk5_0)|(~m1_subset_1(X45,esk6_0)|(~m1_subset_1(X46,esk7_0)|(~m1_subset_1(X47,esk8_0)|(esk10_0!=k4_mcart_1(X44,X45,X46,X47)|esk9_0=X45)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X11, X12, X13, X14]:k4_mcart_1(X11,X12,X13,X14)=k4_tarski(k3_mcart_1(X11,X12,X13),X14), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.14/0.38  cnf(c_0_10, plain, (m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_11, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (esk9_0=X2|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_14, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_12, c_0_11])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_21, plain, (m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (esk9_0=X2|esk10_0!=k4_tarski(k3_mcart_1(X1,X2,X3),X4)|~m1_subset_1(X4,esk8_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_24, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_21, c_0_11])).
% 0.14/0.38  cnf(c_0_25, plain, (m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  fof(c_0_26, plain, ![X19, X20, X21, X22, X23, X24, X25, X26, X27]:((((k8_mcart_1(X19,X20,X21,X22,X23)=X24|X23!=k4_mcart_1(X24,X25,X26,X27)|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22)))&(k9_mcart_1(X19,X20,X21,X22,X23)=X25|X23!=k4_mcart_1(X24,X25,X26,X27)|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))))&(k10_mcart_1(X19,X20,X21,X22,X23)=X26|X23!=k4_mcart_1(X24,X25,X26,X27)|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))))&(k11_mcart_1(X19,X20,X21,X22,X23)=X27|X23!=k4_mcart_1(X24,X25,X26,X27)|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X2|k4_tarski(k3_mcart_1(X3,X2,X4),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))!=esk10_0|~m1_subset_1(X4,esk7_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_29, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_25, c_0_11])).
% 0.14/0.38  cnf(c_0_30, plain, (m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_31, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X6,X8,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_32, plain, (X1=k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X6=k8_mcart_1(X2,X3,X4,X5,X1)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X3|k4_tarski(k3_mcart_1(X4,X3,esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0))!=esk10_0|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X4,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_35, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_30, c_0_11])).
% 0.14/0.38  cnf(c_0_36, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k9_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k3_mcart_1(X7,X6,X8),X9)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_14]), c_0_11])).
% 0.14/0.38  cnf(c_0_37, plain, (X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X6=k8_mcart_1(X2,X3,X4,X5,X1)|X1=k4_tarski(k3_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1)),esk4_6(X2,X3,X4,X5,X6,X1))|~m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_14]), c_0_11])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X3=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k4_tarski(k3_mcart_1(X4,esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0))!=esk10_0|~m1_subset_1(X4,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_40, plain, (k9_mcart_1(X1,X2,X3,X4,k4_tarski(k3_mcart_1(X5,X6,X7),X8))=X6|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(er,[status(thm)],[c_0_36])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (k4_tarski(k3_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))=esk10_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X3=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X4=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k4_tarski(k3_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X4,esk10_0))!=esk10_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (k9_mcart_1(X1,X2,X3,X4,esk10_0)=esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X5,esk10_0)|X5=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (esk9_0!=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 49
% 0.14/0.38  # Proof object clause steps            : 38
% 0.14/0.38  # Proof object formula steps           : 11
% 0.14/0.38  # Proof object conjectures             : 26
% 0.14/0.38  # Proof object clause conjectures      : 23
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 15
% 0.14/0.38  # Proof object initial formulas used   : 5
% 0.14/0.38  # Proof object generating inferences   : 14
% 0.14/0.38  # Proof object simplifying inferences  : 37
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 5
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 38
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 38
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 3
% 0.14/0.38  # Backward-rewritten                   : 30
% 0.14/0.38  # Generated clauses                    : 33
% 0.14/0.38  # ...of the previous two non-trivial   : 37
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 28
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 5
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 5
% 0.14/0.38  #    Positive orientable unit clauses  : 0
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 0
% 0.14/0.38  # Current number of unprocessed clauses: 10
% 0.14/0.38  # ...number of literals in the above   : 48
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 35
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 156
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 17
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 1
% 0.14/0.38  # Rewrite failures with RHS unbound    : 3
% 0.14/0.38  # BW rewrite match attempts            : 67
% 0.14/0.38  # BW rewrite match successes           : 66
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2956
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.007 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
