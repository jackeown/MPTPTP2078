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
% DateTime   : Thu Dec  3 11:00:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 373 expanded)
%              Number of clauses        :   28 ( 120 expanded)
%              Number of leaves         :    3 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  235 (3716 expanded)
%              Number of equality atoms :  172 (2332 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_mcart_1,conjecture,(
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
                         => X5 = X9 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(c_0_3,negated_conjecture,(
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
                           => X5 = X9 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_mcart_1])).

fof(c_0_4,plain,(
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

fof(c_0_5,negated_conjecture,(
    ! [X41,X42,X43,X44] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X41,esk5_0)
        | ~ m1_subset_1(X42,esk6_0)
        | ~ m1_subset_1(X43,esk7_0)
        | ~ m1_subset_1(X44,esk8_0)
        | esk10_0 != k4_mcart_1(X41,X42,X43,X44)
        | esk9_0 = X43 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( esk9_0 = X3
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X4,esk8_0)
    | esk10_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_15,plain,(
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

cnf(c_0_16,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X2
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X3,X2,X4) != esk10_0
    | ~ m1_subset_1(X4,esk8_0)
    | ~ m1_subset_1(X2,esk7_0)
    | ~ m1_subset_1(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X6,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k8_mcart_1(X2,X3,X4,X5,X1)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X3
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X3,X4) != esk10_0
    | ~ m1_subset_1(X4,esk8_0)
    | ~ m1_subset_1(X3,esk7_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,plain,
    ( k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X7
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) = esk10_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X3 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | esk9_0 = X4
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),X4,esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) != esk10_0
    | ~ m1_subset_1(X4,esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk10_0) = esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X5,esk10_0)
    | X5 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X2 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X3 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X4 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X4,esk10_0)) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( esk9_0 != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.13/0.39  # and selection function SelectNegativeLiterals.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t81_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 0.13/0.39  fof(t79_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_mcart_1)).
% 0.13/0.39  fof(t78_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.13/0.39  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t81_mcart_1])).
% 0.13/0.39  fof(c_0_4, plain, ![X25, X26, X27, X28, X29, X30]:((m1_subset_1(esk1_6(X25,X26,X27,X28,X29,X30),X25)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((m1_subset_1(esk2_6(X25,X26,X27,X28,X29,X30),X26)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((m1_subset_1(esk3_6(X25,X26,X27,X28,X29,X30),X27)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((m1_subset_1(esk4_6(X25,X26,X27,X28,X29,X30),X28)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&((X30=k4_mcart_1(esk1_6(X25,X26,X27,X28,X29,X30),esk2_6(X25,X26,X27,X28,X29,X30),esk3_6(X25,X26,X27,X28,X29,X30),esk4_6(X25,X26,X27,X28,X29,X30))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))&(X29!=esk1_6(X25,X26,X27,X28,X29,X30)|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0|X29=k8_mcart_1(X25,X26,X27,X28,X30))|~m1_subset_1(X30,k4_zfmisc_1(X25,X26,X27,X28)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_mcart_1])])])])).
% 0.13/0.39  fof(c_0_5, negated_conjecture, ![X41, X42, X43, X44]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X41,esk5_0)|(~m1_subset_1(X42,esk6_0)|(~m1_subset_1(X43,esk7_0)|(~m1_subset_1(X44,esk8_0)|(esk10_0!=k4_mcart_1(X41,X42,X43,X44)|esk9_0=X43)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.13/0.39  cnf(c_0_6, plain, (m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_7, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_8, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_9, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_10, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_11, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (esk9_0=X3|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_13, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.39  cnf(c_0_14, plain, (m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  fof(c_0_15, plain, ![X16, X17, X18, X19, X20, X21, X22, X23, X24]:((((k8_mcart_1(X16,X17,X18,X19,X20)=X21|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)))&(k9_mcart_1(X16,X17,X18,X19,X20)=X22|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19))))&(k10_mcart_1(X16,X17,X18,X19,X20)=X23|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19))))&(k11_mcart_1(X16,X17,X18,X19,X20)=X24|X20!=k4_mcart_1(X21,X22,X23,X24)|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0|X19=k1_xboole_0)|~m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X2|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X3,X2,X4)!=esk10_0|~m1_subset_1(X4,esk8_0)|~m1_subset_1(X2,esk7_0)|~m1_subset_1(X3,esk6_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.39  cnf(c_0_18, plain, (m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_19, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X6,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_20, plain, (X1=k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X6=k8_mcart_1(X2,X3,X4,X5,X1)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X3|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),X3,X4)!=esk10_0|~m1_subset_1(X4,esk8_0)|~m1_subset_1(X3,esk7_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.39  cnf(c_0_23, plain, (m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_24, plain, (k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X7|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))=esk10_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X3=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|esk9_0=X4|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),X4,esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))!=esk10_0|~m1_subset_1(X4,esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (k10_mcart_1(X1,X2,X3,X4,esk10_0)=esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X5,esk10_0)|X5=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X2=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X3=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X4=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k4_mcart_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X3,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X2,esk10_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X4,esk10_0))!=esk10_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (esk9_0!=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 35
% 0.13/0.39  # Proof object clause steps            : 28
% 0.13/0.39  # Proof object formula steps           : 7
% 0.13/0.39  # Proof object conjectures             : 24
% 0.13/0.39  # Proof object clause conjectures      : 21
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 13
% 0.13/0.39  # Proof object initial formulas used   : 3
% 0.13/0.39  # Proof object generating inferences   : 13
% 0.13/0.39  # Proof object simplifying inferences  : 28
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 4
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 21
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 21
% 0.13/0.39  # Processed clauses                    : 206
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 77
% 0.13/0.39  # ...remaining for further processing  : 129
% 0.13/0.39  # Other redundant clauses eliminated   : 4
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 13
% 0.13/0.39  # Backward-rewritten                   : 85
% 0.13/0.39  # Generated clauses                    : 317
% 0.13/0.39  # ...of the previous two non-trivial   : 314
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 312
% 0.13/0.39  # Factorizations                       : 1
% 0.13/0.39  # Equation resolutions                 : 4
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 6
% 0.13/0.39  #    Positive orientable unit clauses  : 1
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 4
% 0.13/0.39  #    Non-unit-clauses                  : 0
% 0.13/0.39  # Current number of unprocessed clauses: 131
% 0.13/0.39  # ...number of literals in the above   : 723
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 119
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1685
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 165
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 87
% 0.13/0.39  # Unit Clause-clause subsumption calls : 7
% 0.13/0.39  # Rewrite failures with RHS unbound    : 3
% 0.13/0.39  # BW rewrite match attempts            : 118
% 0.13/0.39  # BW rewrite match successes           : 113
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 14148
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.049 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
