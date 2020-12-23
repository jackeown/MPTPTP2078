%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 252 expanded)
%              Number of clauses        :   36 (  91 expanded)
%              Number of leaves         :    5 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  245 (1838 expanded)
%              Number of equality atoms :  168 (1137 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_mcart_1,conjecture,(
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

fof(l68_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ! [X8] :
                        ( m1_subset_1(X8,X3)
                       => ! [X9] :
                            ( m1_subset_1(X9,X4)
                           => X5 != k4_mcart_1(X6,X7,X8,X9) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

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
                           => X5 = X7 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k8_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t79_mcart_1])).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( m1_subset_1(esk1_5(X19,X20,X21,X22,X23),X19)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( m1_subset_1(esk2_5(X19,X20,X21,X22,X23),X20)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( m1_subset_1(esk3_5(X19,X20,X21,X22,X23),X21)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( m1_subset_1(esk4_5(X19,X20,X21,X22,X23),X22)
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X23 = k4_mcart_1(esk1_5(X19,X20,X21,X22,X23),esk2_5(X19,X20,X21,X22,X23),esk3_5(X19,X20,X21,X22,X23),esk4_5(X19,X20,X21,X22,X23))
        | ~ m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

fof(c_0_7,plain,(
    ! [X15,X16,X17,X18] : k4_zfmisc_1(X15,X16,X17,X18) = k2_zfmisc_1(k3_zfmisc_1(X15,X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_8,negated_conjecture,(
    ! [X43,X44,X45,X46] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X43,esk5_0)
        | ~ m1_subset_1(X44,esk6_0)
        | ~ m1_subset_1(X45,esk7_0)
        | ~ m1_subset_1(X46,esk8_0)
        | esk10_0 != k4_mcart_1(X43,X44,X45,X46)
        | esk9_0 = X43 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14] : k4_mcart_1(X11,X12,X13,X14) = k4_tarski(k3_mcart_1(X11,X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk9_0 = X1
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
    | m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
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
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( esk9_0 = X1
    | esk10_0 != k4_tarski(k3_mcart_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X4,esk8_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( esk9_0 = X1
    | k4_tarski(k3_mcart_1(X1,X2,X3),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) != esk10_0
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( X1 = k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_31,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( k8_mcart_1(X28,X29,X30,X31,X32) = X33
        | X32 != k4_mcart_1(X33,X34,X35,X36)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( k9_mcart_1(X28,X29,X30,X31,X32) = X34
        | X32 != k4_mcart_1(X33,X34,X35,X36)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( k10_mcart_1(X28,X29,X30,X31,X32) = X35
        | X32 != k4_mcart_1(X33,X34,X35,X36)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31)) )
      & ( k11_mcart_1(X28,X29,X30,X31,X32) = X36
        | X32 != k4_mcart_1(X33,X34,X35,X36)
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( esk9_0 = X1
    | k4_tarski(k3_mcart_1(X1,X2,esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) != esk10_0
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_34,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_11])).

cnf(c_0_35,plain,
    ( X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_tarski(k3_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1)),esk4_5(X2,X3,X4,X5,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_14]),c_0_11])).

cnf(c_0_36,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X6,X7,X8,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( esk9_0 = X1
    | k4_tarski(k3_mcart_1(X1,esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) != esk10_0
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(k3_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) = esk10_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_40,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_14]),c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_42,plain,
    ( k8_mcart_1(X1,X2,X3,X4,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X5
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k4_tarski(k3_mcart_1(esk9_0,esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( k8_mcart_1(X1,X2,X3,X4,esk10_0) = esk9_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( esk9_0 != k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_45]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:42:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_RG_S070I
% 0.19/0.37  # and selection function SelectVGNonCR.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.029 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t79_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 0.19/0.37  fof(l68_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>![X9]:(m1_subset_1(X9,X4)=>X5!=k4_mcart_1(X6,X7,X8,X9)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 0.19/0.37  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.19/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.19/0.37  fof(t78_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t79_mcart_1])).
% 0.19/0.37  fof(c_0_6, plain, ![X19, X20, X21, X22, X23]:((m1_subset_1(esk1_5(X19,X20,X21,X22,X23),X19)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((m1_subset_1(esk2_5(X19,X20,X21,X22,X23),X20)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((m1_subset_1(esk3_5(X19,X20,X21,X22,X23),X21)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((m1_subset_1(esk4_5(X19,X20,X21,X22,X23),X22)|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&(X23=k4_mcart_1(esk1_5(X19,X20,X21,X22,X23),esk2_5(X19,X20,X21,X22,X23),esk3_5(X19,X20,X21,X22,X23),esk4_5(X19,X20,X21,X22,X23))|~m1_subset_1(X23,k4_zfmisc_1(X19,X20,X21,X22))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X15, X16, X17, X18]:k4_zfmisc_1(X15,X16,X17,X18)=k2_zfmisc_1(k3_zfmisc_1(X15,X16,X17),X18), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ![X43, X44, X45, X46]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X43,esk5_0)|(~m1_subset_1(X44,esk6_0)|(~m1_subset_1(X45,esk7_0)|(~m1_subset_1(X46,esk8_0)|(esk10_0!=k4_mcart_1(X43,X44,X45,X46)|esk9_0=X43)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.19/0.37  fof(c_0_9, plain, ![X11, X12, X13, X14]:k4_mcart_1(X11,X12,X13,X14)=k4_tarski(k3_mcart_1(X11,X12,X13),X14), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.19/0.37  cnf(c_0_10, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (esk9_0=X1|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_14, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_15, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_12, c_0_11])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_21, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (esk9_0=X1|esk10_0!=k4_tarski(k3_mcart_1(X1,X2,X3),X4)|~m1_subset_1(X4,esk8_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_24, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_21, c_0_11])).
% 0.19/0.37  cnf(c_0_25, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (esk9_0=X1|k4_tarski(k3_mcart_1(X1,X2,X3),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))!=esk10_0|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_28, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_25, c_0_11])).
% 0.19/0.37  cnf(c_0_29, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_30, plain, (X1=k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  fof(c_0_31, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36]:((((k8_mcart_1(X28,X29,X30,X31,X32)=X33|X32!=k4_mcart_1(X33,X34,X35,X36)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0)|~m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31)))&(k9_mcart_1(X28,X29,X30,X31,X32)=X34|X32!=k4_mcart_1(X33,X34,X35,X36)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0)|~m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31))))&(k10_mcart_1(X28,X29,X30,X31,X32)=X35|X32!=k4_mcart_1(X33,X34,X35,X36)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0)|~m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31))))&(k11_mcart_1(X28,X29,X30,X31,X32)=X36|X32!=k4_mcart_1(X33,X34,X35,X36)|(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0)|~m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (esk9_0=X1|k4_tarski(k3_mcart_1(X1,X2,esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))!=esk10_0|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_34, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_29, c_0_11])).
% 0.19/0.37  cnf(c_0_35, plain, (X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_tarski(k3_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1)),esk4_5(X2,X3,X4,X5,X1))|~m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_14]), c_0_11])).
% 0.19/0.37  cnf(c_0_36, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X6,X7,X8,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (esk9_0=X1|k4_tarski(k3_mcart_1(X1,esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))!=esk10_0|~m1_subset_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (k4_tarski(k3_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))=esk10_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_40, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k8_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k3_mcart_1(X6,X7,X8),X9)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_14]), c_0_11])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.37  cnf(c_0_42, plain, (k8_mcart_1(X1,X2,X3,X4,k4_tarski(k3_mcart_1(X5,X6,X7),X8))=X5|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (k4_tarski(k3_mcart_1(esk9_0,esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))=esk10_0), inference(rw,[status(thm)],[c_0_39, c_0_41])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (k8_mcart_1(X1,X2,X3,X4,esk10_0)=esk9_0|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (esk9_0!=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_45]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 47
% 0.19/0.37  # Proof object clause steps            : 36
% 0.19/0.37  # Proof object formula steps           : 11
% 0.19/0.37  # Proof object conjectures             : 24
% 0.19/0.37  # Proof object clause conjectures      : 21
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 15
% 0.19/0.37  # Proof object initial formulas used   : 5
% 0.19/0.37  # Proof object generating inferences   : 12
% 0.19/0.37  # Proof object simplifying inferences  : 38
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 5
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 18
% 0.19/0.37  # Removed in clause preprocessing      : 2
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 34
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 34
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 32
% 0.19/0.37  # ...of the previous two non-trivial   : 33
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 26
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 6
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
% 0.19/0.37  # Current number of processed clauses  : 32
% 0.19/0.37  #    Positive orientable unit clauses  : 7
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 5
% 0.19/0.37  #    Non-unit-clauses                  : 20
% 0.19/0.37  # Current number of unprocessed clauses: 15
% 0.19/0.37  # ...number of literals in the above   : 96
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 4
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 32
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 4
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2351
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.028 s
% 0.19/0.37  # System time              : 0.007 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
