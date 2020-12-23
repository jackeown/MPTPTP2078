%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:18 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 563 expanded)
%              Number of clauses        :   40 ( 211 expanded)
%              Number of leaves         :    7 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  285 (3403 expanded)
%              Number of equality atoms :  212 (2226 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X8 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(t69_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X6 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t68_mcart_1,axiom,(
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

fof(t51_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X8 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_mcart_1])).

fof(c_0_8,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( m1_subset_1(esk1_5(X30,X31,X32,X33,X34),X30)
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k5_mcart_1(X30,X31,X32,X34)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)) )
      & ( m1_subset_1(esk2_5(X30,X31,X32,X33,X34),X31)
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k5_mcart_1(X30,X31,X32,X34)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)) )
      & ( m1_subset_1(esk3_5(X30,X31,X32,X33,X34),X32)
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k5_mcart_1(X30,X31,X32,X34)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)) )
      & ( X34 = k3_mcart_1(esk1_5(X30,X31,X32,X33,X34),esk2_5(X30,X31,X32,X33,X34),esk3_5(X30,X31,X32,X33,X34))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k5_mcart_1(X30,X31,X32,X34)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)) )
      & ( X33 != esk1_5(X30,X31,X32,X33,X34)
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k5_mcart_1(X30,X31,X32,X34)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_mcart_1])])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,negated_conjecture,(
    ! [X43,X44,X45] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X43,esk4_0)
        | ~ m1_subset_1(X44,esk5_0)
        | ~ m1_subset_1(X45,esk6_0)
        | esk8_0 != k3_mcart_1(X43,X44,X45)
        | esk7_0 = X45 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k5_mcart_1(X1,X2,X3,X5)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( esk7_0 = X3
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k5_mcart_1(X1,X2,X3,X5)
    | m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k5_mcart_1(X1,X2,X3,X5)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( esk7_0 = X3
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | m1_subset_1(esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k5_mcart_1(X1,X2,X3,X5)
    | m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k5_mcart_1(X1,X2,X3,X5)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0) = esk7_0
    | X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k4_tarski(k4_tarski(X2,X3),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)) != esk8_0
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | m1_subset_1(esk2_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_29,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k5_mcart_1(X1,X2,X3,X5)
    | m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_30,plain,
    ( X1 = k3_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k5_mcart_1(X2,X3,X4,X1)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_31,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29] :
      ( ( k5_mcart_1(X23,X24,X25,X26) = X27
        | X26 != k3_mcart_1(X27,X28,X29)
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25)) )
      & ( k6_mcart_1(X23,X24,X25,X26) = X28
        | X26 != k3_mcart_1(X27,X28,X29)
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25)) )
      & ( k7_mcart_1(X23,X24,X25,X26) = X29
        | X26 != k3_mcart_1(X27,X28,X29)
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_mcart_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0) = esk7_0
    | X2 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k4_tarski(k4_tarski(X3,esk2_5(esk4_0,esk5_0,esk6_0,X2,esk8_0)),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)) != esk8_0
    | ~ m1_subset_1(X3,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_34,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X5 = k5_mcart_1(X2,X3,X4,X1)
    | X1 = k4_tarski(k4_tarski(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1)),esk3_5(X2,X3,X4,X5,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_16]),c_0_13])).

fof(c_0_35,plain,(
    ! [X15,X16,X17,X18] :
      ( ( k5_mcart_1(X15,X16,X17,X18) = k1_mcart_1(k1_mcart_1(X18))
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( k6_mcart_1(X15,X16,X17,X18) = k2_mcart_1(k1_mcart_1(X18))
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( k7_mcart_1(X15,X16,X17,X18) = k2_mcart_1(X18)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_36,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X7,X5)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0) = esk7_0
    | X2 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | X3 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k4_tarski(k4_tarski(esk1_5(esk4_0,esk5_0,esk6_0,X2,esk8_0),esk2_5(esk4_0,esk5_0,esk6_0,X3,esk8_0)),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk2_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)) = esk8_0
    | X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_39,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X22 != k5_mcart_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X22 != k6_mcart_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X22 != k7_mcart_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_mcart_1])])])])).

cnf(c_0_41,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k4_tarski(k4_tarski(X6,X7),X5)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_16]),c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0) = esk7_0
    | X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_13])).

cnf(c_0_44,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k7_mcart_1(X2,X3,X4,X1)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k7_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk2_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)),esk7_0) = esk8_0
    | X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_49,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 != k7_mcart_1(X2,X3,X4,X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k7_mcart_1(X2,X3,X4,esk8_0) = esk7_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k2_mcart_1(esk8_0) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_mcart_1(esk8_0) != esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_18])]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_48]),c_0_51]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_RG_S070I
% 0.14/0.39  # and selection function SelectVGNonCR.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.041 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.14/0.39  fof(t69_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.14/0.39  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.14/0.39  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.14/0.39  fof(t68_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_mcart_1)).
% 0.14/0.39  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.14/0.39  fof(t51_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.14/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.14/0.39  fof(c_0_8, plain, ![X30, X31, X32, X33, X34]:((m1_subset_1(esk1_5(X30,X31,X32,X33,X34),X30)|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0|X33=k5_mcart_1(X30,X31,X32,X34))|~m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)))&((m1_subset_1(esk2_5(X30,X31,X32,X33,X34),X31)|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0|X33=k5_mcart_1(X30,X31,X32,X34))|~m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)))&((m1_subset_1(esk3_5(X30,X31,X32,X33,X34),X32)|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0|X33=k5_mcart_1(X30,X31,X32,X34))|~m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)))&((X34=k3_mcart_1(esk1_5(X30,X31,X32,X33,X34),esk2_5(X30,X31,X32,X33,X34),esk3_5(X30,X31,X32,X33,X34))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0|X33=k5_mcart_1(X30,X31,X32,X34))|~m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32)))&(X33!=esk1_5(X30,X31,X32,X33,X34)|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0|X33=k5_mcart_1(X30,X31,X32,X34))|~m1_subset_1(X34,k3_zfmisc_1(X30,X31,X32))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_mcart_1])])])])).
% 0.14/0.39  fof(c_0_9, plain, ![X12, X13, X14]:k3_zfmisc_1(X12,X13,X14)=k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.14/0.39  fof(c_0_10, negated_conjecture, ![X43, X44, X45]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X43,esk4_0)|(~m1_subset_1(X44,esk5_0)|(~m1_subset_1(X45,esk6_0)|(esk8_0!=k3_mcart_1(X43,X44,X45)|esk7_0=X45))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.14/0.39  fof(c_0_11, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.14/0.39  cnf(c_0_12, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)|~m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_15, negated_conjecture, (esk7_0=X3|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_16, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_17, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)|m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_14, c_0_13])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_22, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)|~m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (esk7_0=X3|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|m1_subset_1(esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_25, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)|m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_22, c_0_13])).
% 0.14/0.39  cnf(c_0_26, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)|~m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)=esk7_0|X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|k4_tarski(k4_tarski(X2,X3),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0))!=esk8_0|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X2,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|m1_subset_1(esk2_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_29, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)|m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_26, c_0_13])).
% 0.14/0.39  cnf(c_0_30, plain, (X1=k3_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k5_mcart_1(X2,X3,X4,X1)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  fof(c_0_31, plain, ![X23, X24, X25, X26, X27, X28, X29]:(((k5_mcart_1(X23,X24,X25,X26)=X27|X26!=k3_mcart_1(X27,X28,X29)|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25)))&(k6_mcart_1(X23,X24,X25,X26)=X28|X26!=k3_mcart_1(X27,X28,X29)|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))))&(k7_mcart_1(X23,X24,X25,X26)=X29|X26!=k3_mcart_1(X27,X28,X29)|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_mcart_1])])])])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)=esk7_0|X2=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|k4_tarski(k4_tarski(X3,esk2_5(esk4_0,esk5_0,esk6_0,X2,esk8_0)),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0))!=esk8_0|~m1_subset_1(X3,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_34, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X5=k5_mcart_1(X2,X3,X4,X1)|X1=k4_tarski(k4_tarski(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1)),esk3_5(X2,X3,X4,X5,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_16]), c_0_13])).
% 0.14/0.39  fof(c_0_35, plain, ![X15, X16, X17, X18]:(((k5_mcart_1(X15,X16,X17,X18)=k1_mcart_1(k1_mcart_1(X18))|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&(k6_mcart_1(X15,X16,X17,X18)=k2_mcart_1(k1_mcart_1(X18))|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0)))&(k7_mcart_1(X15,X16,X17,X18)=k2_mcart_1(X18)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.14/0.39  cnf(c_0_36, plain, (k7_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X7,X5)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)=esk7_0|X2=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|X3=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|k4_tarski(k4_tarski(esk1_5(esk4_0,esk5_0,esk6_0,X2,esk8_0),esk2_5(esk4_0,esk5_0,esk6_0,X3,esk8_0)),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0))!=esk8_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (k4_tarski(k4_tarski(esk1_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk2_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)),esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0))=esk8_0|X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_39, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  fof(c_0_40, plain, ![X19, X20, X21, X22]:(((X22!=k5_mcart_1(X19,X20,X21,X22)|~m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0))&(X22!=k6_mcart_1(X19,X20,X21,X22)|~m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0)))&(X22!=k7_mcart_1(X19,X20,X21,X22)|~m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_mcart_1])])])])).
% 0.14/0.39  cnf(c_0_41, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=X5|X4!=k4_tarski(k4_tarski(X6,X7),X5)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_16]), c_0_13])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (esk3_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)=esk7_0|X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.39  cnf(c_0_43, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_39, c_0_13])).
% 0.14/0.39  cnf(c_0_44, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=k7_mcart_1(X2,X3,X4,X1)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.39  cnf(c_0_45, plain, (k7_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6))=X6|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_41])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (k4_tarski(k4_tarski(esk1_5(esk4_0,esk5_0,esk6_0,X1,esk8_0),esk2_5(esk4_0,esk5_0,esk6_0,X1,esk8_0)),esk7_0)=esk8_0|X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (esk7_0!=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_49, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1!=k7_mcart_1(X2,X3,X4,X1)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_44, c_0_13])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|k7_mcart_1(X2,X3,X4,esk8_0)=esk7_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (k2_mcart_1(esk8_0)!=esk7_0), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (k2_mcart_1(esk8_0)!=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_18])]), c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (X1=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_18]), c_0_48]), c_0_51]), c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.40  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 55
% 0.14/0.40  # Proof object clause steps            : 40
% 0.14/0.40  # Proof object formula steps           : 15
% 0.14/0.40  # Proof object conjectures             : 26
% 0.14/0.40  # Proof object clause conjectures      : 23
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 15
% 0.14/0.40  # Proof object initial formulas used   : 7
% 0.14/0.40  # Proof object generating inferences   : 14
% 0.14/0.40  # Proof object simplifying inferences  : 39
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 7
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 22
% 0.14/0.40  # Removed in clause preprocessing      : 2
% 0.14/0.40  # Initial clauses in saturation        : 20
% 0.14/0.40  # Processed clauses                    : 44
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 0
% 0.14/0.40  # ...remaining for further processing  : 44
% 0.14/0.40  # Other redundant clauses eliminated   : 0
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 4
% 0.14/0.40  # Backward-rewritten                   : 36
% 0.14/0.40  # Generated clauses                    : 47
% 0.14/0.40  # ...of the previous two non-trivial   : 55
% 0.14/0.40  # Contextual simplify-reflections      : 0
% 0.14/0.40  # Paramodulations                      : 41
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 6
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 4
% 0.14/0.40  #    Positive orientable unit clauses  : 0
% 0.14/0.40  #    Positive unorientable unit clauses: 1
% 0.14/0.40  #    Negative unit clauses             : 3
% 0.14/0.40  #    Non-unit-clauses                  : 0
% 0.14/0.40  # Current number of unprocessed clauses: 22
% 0.14/0.40  # ...number of literals in the above   : 141
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 42
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 230
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 19
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.40  # Unit Clause-clause subsumption calls : 26
% 0.14/0.40  # Rewrite failures with RHS unbound    : 3
% 0.14/0.40  # BW rewrite match attempts            : 64
% 0.14/0.40  # BW rewrite match successes           : 63
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 3029
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.043 s
% 0.14/0.40  # System time              : 0.010 s
% 0.14/0.40  # Total time               : 0.053 s
% 0.14/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
