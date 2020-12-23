%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:29 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 305 expanded)
%              Number of clauses        :   39 ( 110 expanded)
%              Number of leaves         :    5 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  285 (2299 expanded)
%              Number of equality atoms :  205 (1434 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

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
                           => X5 = X9 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_mcart_1])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( m1_subset_1(esk1_5(X15,X16,X17,X18,X19),X15)
        | ~ m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( m1_subset_1(esk2_5(X15,X16,X17,X18,X19),X16)
        | ~ m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( m1_subset_1(esk3_5(X15,X16,X17,X18,X19),X17)
        | ~ m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( m1_subset_1(esk4_5(X15,X16,X17,X18,X19),X18)
        | ~ m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X19 = k4_mcart_1(esk1_5(X15,X16,X17,X18,X19),esk2_5(X15,X16,X17,X18,X19),esk3_5(X15,X16,X17,X18,X19),esk4_5(X15,X16,X17,X18,X19))
        | ~ m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14] : k4_zfmisc_1(X11,X12,X13,X14) = k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_8,negated_conjecture,(
    ! [X44,X45,X46,X47] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X44,esk5_0)
        | ~ m1_subset_1(X45,esk6_0)
        | ~ m1_subset_1(X46,esk7_0)
        | ~ m1_subset_1(X47,esk8_0)
        | esk10_0 != k4_mcart_1(X44,X45,X46,X47)
        | esk9_0 = X46 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( esk9_0 = X3
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X4,esk8_0)
    | esk10_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_10])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( esk9_0 = X1
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X2,X1,X3) != esk10_0
    | ~ m1_subset_1(X3,esk8_0)
    | ~ m1_subset_1(X1,esk7_0)
    | ~ m1_subset_1(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_25,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_10])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( esk9_0 = X1
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X1,X2) != esk10_0
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_29,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_10])).

cnf(c_0_30,plain,
    ( X1 = k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_31,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( k8_mcart_1(X29,X30,X31,X32,X33) = X34
        | X33 != k4_mcart_1(X34,X35,X36,X37)
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32)) )
      & ( k9_mcart_1(X29,X30,X31,X32,X33) = X35
        | X33 != k4_mcart_1(X34,X35,X36,X37)
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32)) )
      & ( k10_mcart_1(X29,X30,X31,X32,X33) = X36
        | X33 != k4_mcart_1(X34,X35,X36,X37)
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32)) )
      & ( k11_mcart_1(X29,X30,X31,X32,X33) = X37
        | X33 != k4_mcart_1(X34,X35,X36,X37)
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = esk9_0
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X1) != esk10_0
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_34,plain,
    ( X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_10])).

fof(c_0_35,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( k8_mcart_1(X24,X25,X26,X27,X28) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X28)))
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k9_mcart_1(X24,X25,X26,X27,X28) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X28)))
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k10_mcart_1(X24,X25,X26,X27,X28) = k2_mcart_1(k1_mcart_1(X28))
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k11_mcart_1(X24,X25,X26,X27,X28) = k2_mcart_1(X28)
        | ~ m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_36,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X6,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = esk9_0
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) = esk10_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_39,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_mcart_1(X7,X8,X6,X9)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_42,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_10])).

cnf(c_0_43,plain,
    ( k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X7
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk9_0,esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( esk9_0 != k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = k2_mcart_1(k1_mcart_1(esk10_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk10_0) = esk9_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk10_0)) != esk9_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_13]),c_0_46]),c_0_48]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:21:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.12/0.37  # and selection function SelectNegativeLiterals.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t81_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_mcart_1)).
% 0.12/0.37  fof(l68_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>![X9]:(m1_subset_1(X9,X4)=>X5!=k4_mcart_1(X6,X7,X8,X9)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 0.12/0.37  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.12/0.37  fof(t78_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.12/0.37  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t81_mcart_1])).
% 0.12/0.37  fof(c_0_6, plain, ![X15, X16, X17, X18, X19]:((m1_subset_1(esk1_5(X15,X16,X17,X18,X19),X15)|~m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))&((m1_subset_1(esk2_5(X15,X16,X17,X18,X19),X16)|~m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))&((m1_subset_1(esk3_5(X15,X16,X17,X18,X19),X17)|~m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))&((m1_subset_1(esk4_5(X15,X16,X17,X18,X19),X18)|~m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0))&(X19=k4_mcart_1(esk1_5(X15,X16,X17,X18,X19),esk2_5(X15,X16,X17,X18,X19),esk3_5(X15,X16,X17,X18,X19),esk4_5(X15,X16,X17,X18,X19))|~m1_subset_1(X19,k4_zfmisc_1(X15,X16,X17,X18))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X11, X12, X13, X14]:k4_zfmisc_1(X11,X12,X13,X14)=k2_zfmisc_1(k3_zfmisc_1(X11,X12,X13),X14), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ![X44, X45, X46, X47]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X44,esk5_0)|(~m1_subset_1(X45,esk6_0)|(~m1_subset_1(X46,esk7_0)|(~m1_subset_1(X47,esk8_0)|(esk10_0!=k4_mcart_1(X44,X45,X46,X47)|esk9_0=X46)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.12/0.37  cnf(c_0_9, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_10, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_11, c_0_10])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_18, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (esk9_0=X3|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])).
% 0.12/0.37  cnf(c_0_21, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_18, c_0_10])).
% 0.12/0.37  cnf(c_0_22, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (esk9_0=X1|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X2,X1,X3)!=esk10_0|~m1_subset_1(X3,esk8_0)|~m1_subset_1(X1,esk7_0)|~m1_subset_1(X2,esk6_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])).
% 0.12/0.37  cnf(c_0_25, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_22, c_0_10])).
% 0.12/0.37  cnf(c_0_26, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (esk9_0=X1|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X1,X2)!=esk10_0|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X1,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])).
% 0.12/0.37  cnf(c_0_29, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_26, c_0_10])).
% 0.12/0.37  cnf(c_0_30, plain, (X1=k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  fof(c_0_31, plain, ![X29, X30, X31, X32, X33, X34, X35, X36, X37]:((((k8_mcart_1(X29,X30,X31,X32,X33)=X34|X33!=k4_mcart_1(X34,X35,X36,X37)|(X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0)|~m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32)))&(k9_mcart_1(X29,X30,X31,X32,X33)=X35|X33!=k4_mcart_1(X34,X35,X36,X37)|(X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0)|~m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32))))&(k10_mcart_1(X29,X30,X31,X32,X33)=X36|X33!=k4_mcart_1(X34,X35,X36,X37)|(X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0)|~m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32))))&(k11_mcart_1(X29,X30,X31,X32,X33)=X37|X33!=k4_mcart_1(X34,X35,X36,X37)|(X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0)|~m1_subset_1(X33,k4_zfmisc_1(X29,X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=esk9_0|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X1)!=esk10_0|~m1_subset_1(X1,esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])).
% 0.12/0.37  cnf(c_0_34, plain, (X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))|~m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5))), inference(rw,[status(thm)],[c_0_30, c_0_10])).
% 0.12/0.37  fof(c_0_35, plain, ![X24, X25, X26, X27, X28]:((((k8_mcart_1(X24,X25,X26,X27,X28)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X28)))|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))&(k9_mcart_1(X24,X25,X26,X27,X28)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X28)))|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0)))&(k10_mcart_1(X24,X25,X26,X27,X28)=k2_mcart_1(k1_mcart_1(X28))|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0)))&(k11_mcart_1(X24,X25,X26,X27,X28)=k2_mcart_1(X28)|~m1_subset_1(X28,k4_zfmisc_1(X24,X25,X26,X27))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.12/0.37  cnf(c_0_36, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X6,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=esk9_0|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))!=esk10_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))=esk10_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])).
% 0.12/0.37  cnf(c_0_39, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_40, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k10_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_mcart_1(X7,X8,X6,X9)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_36, c_0_10])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.12/0.37  cnf(c_0_42, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_39, c_0_10])).
% 0.12/0.37  cnf(c_0_43, plain, (k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X7|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(er,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk9_0,esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))=esk10_0), inference(rw,[status(thm)],[c_0_38, c_0_41])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (esk9_0!=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=k2_mcart_1(k1_mcart_1(esk10_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (k10_mcart_1(X1,X2,X3,X4,esk10_0)=esk9_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk10_0))!=esk9_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_13]), c_0_46]), c_0_48]), c_0_14]), c_0_15]), c_0_16]), c_0_17]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 50
% 0.12/0.37  # Proof object clause steps            : 39
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 26
% 0.12/0.37  # Proof object clause conjectures      : 23
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 12
% 0.12/0.37  # Proof object simplifying inferences  : 43
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 21
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 20
% 0.12/0.37  # Processed clauses                    : 90
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 17
% 0.12/0.37  # ...remaining for further processing  : 73
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 11
% 0.12/0.37  # Generated clauses                    : 54
% 0.12/0.37  # ...of the previous two non-trivial   : 57
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 50
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 4
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
% 0.12/0.37  # Current number of processed clauses  : 38
% 0.12/0.37  #    Positive orientable unit clauses  : 11
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 5
% 0.12/0.37  #    Non-unit-clauses                  : 22
% 0.12/0.37  # Current number of unprocessed clauses: 7
% 0.12/0.37  # ...number of literals in the above   : 42
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 32
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 84
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 17
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 17
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 10
% 0.12/0.37  # BW rewrite match successes           : 3
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4030
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.033 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
