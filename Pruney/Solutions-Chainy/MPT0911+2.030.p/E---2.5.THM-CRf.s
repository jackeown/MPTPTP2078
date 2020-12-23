%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 203 expanded)
%              Number of clauses        :   34 (  77 expanded)
%              Number of leaves         :    6 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 (1152 expanded)
%              Number of equality atoms :  132 ( 719 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   22 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(l44_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ! [X5] :
                ( m1_subset_1(X5,X1)
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ! [X7] :
                        ( m1_subset_1(X7,X3)
                       => X4 != k3_mcart_1(X5,X6,X7) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d7_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X3)
                 => ( X5 = k7_mcart_1(X1,X2,X3,X4)
                  <=> ! [X6,X7,X8] :
                        ( X4 = k3_mcart_1(X6,X7,X8)
                       => X5 = X8 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X30,X31,X32,X33] :
      ( ( m1_subset_1(esk4_4(X30,X31,X32,X33),X30)
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( m1_subset_1(esk5_4(X30,X31,X32,X33),X31)
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( m1_subset_1(esk6_4(X30,X31,X32,X33),X32)
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( X33 = k3_mcart_1(esk4_4(X30,X31,X32,X33),esk5_4(X30,X31,X32,X33),esk6_4(X30,X31,X32,X33))
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_8,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,negated_conjecture,(
    ! [X42,X43,X44] :
      ( m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
      & ( ~ m1_subset_1(X42,esk7_0)
        | ~ m1_subset_1(X43,esk8_0)
        | ~ m1_subset_1(X44,esk9_0)
        | esk11_0 != k3_mcart_1(X42,X43,X44)
        | esk10_0 = X44 )
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k1_xboole_0
      & esk10_0 != k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( X19 != k7_mcart_1(X15,X16,X17,X18)
        | X18 != k3_mcart_1(X20,X21,X22)
        | X19 = X22
        | ~ m1_subset_1(X19,X17)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X18 = k3_mcart_1(esk1_5(X15,X16,X17,X18,X19),esk2_5(X15,X16,X17,X18,X19),esk3_5(X15,X16,X17,X18,X19))
        | X19 = k7_mcart_1(X15,X16,X17,X18)
        | ~ m1_subset_1(X19,X17)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X19 != esk3_5(X15,X16,X17,X18,X19)
        | X19 = k7_mcart_1(X15,X16,X17,X18)
        | ~ m1_subset_1(X19,X17)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_mcart_1])])])])])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk6_4(X1,X2,X3,X4),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = X8
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k7_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X4)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))
      | m1_subset_1(k7_mcart_1(X26,X27,X28,X29),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_18,negated_conjecture,
    ( esk10_0 = X3
    | ~ m1_subset_1(X1,esk7_0)
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X3,esk9_0)
    | esk11_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk6_4(X1,X2,X3,X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( X1 = X8
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 != k7_mcart_1(X2,X3,X4,X5)
    | X5 != k4_tarski(k4_tarski(X6,X7),X8)
    | ~ m1_subset_1(X1,X4)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_13])).

cnf(c_0_26,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( X1 = k3_mcart_1(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( esk10_0 = X3
    | esk11_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk9_0)
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_4(esk7_0,esk8_0,esk9_0,esk11_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk5_4(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = X5
    | X4 != k7_mcart_1(X3,X2,X1,k4_tarski(k4_tarski(X6,X7),X5))
    | ~ m1_subset_1(k4_tarski(k4_tarski(X6,X7),X5),k2_zfmisc_1(k2_zfmisc_1(X3,X2),X1))
    | ~ m1_subset_1(X4,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_34,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_tarski(k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1)),esk6_4(X2,X3,X4,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_16]),c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( esk6_4(esk7_0,esk8_0,esk9_0,esk11_0) = esk10_0
    | k4_tarski(k4_tarski(X1,X2),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) != esk11_0
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_37,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk4_4(X1,X2,X3,X4),X1)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_13])).

cnf(c_0_38,plain,
    ( k7_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6)) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(k4_tarski(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk5_4(esk7_0,esk8_0,esk9_0,esk11_0)),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) = esk11_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( esk6_4(esk7_0,esk8_0,esk9_0,esk11_0) = esk10_0
    | k4_tarski(k4_tarski(X1,esk5_4(esk7_0,esk8_0,esk9_0,esk11_0)),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) != esk11_0
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk11_0) = esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( esk6_4(esk7_0,esk8_0,esk9_0,esk11_0) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk11_0) = esk10_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( esk10_0 != k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_45]),c_0_21]),c_0_22]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:51:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_RG_S070I
% 0.13/0.37  # and selection function SelectVGNonCR.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.021 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.13/0.37  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(d7_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>![X5]:(m1_subset_1(X5,X3)=>(X5=k7_mcart_1(X1,X2,X3,X4)<=>![X6, X7, X8]:(X4=k3_mcart_1(X6,X7,X8)=>X5=X8))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_mcart_1)).
% 0.13/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.37  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.13/0.37  fof(c_0_7, plain, ![X30, X31, X32, X33]:((m1_subset_1(esk4_4(X30,X31,X32,X33),X30)|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))&((m1_subset_1(esk5_4(X30,X31,X32,X33),X31)|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))&((m1_subset_1(esk6_4(X30,X31,X32,X33),X32)|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))&(X33=k3_mcart_1(esk4_4(X30,X31,X32,X33),esk5_4(X30,X31,X32,X33),esk6_4(X30,X31,X32,X33))|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X12, X13, X14]:k3_zfmisc_1(X12,X13,X14)=k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, ![X42, X43, X44]:(m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&((~m1_subset_1(X42,esk7_0)|(~m1_subset_1(X43,esk8_0)|(~m1_subset_1(X44,esk9_0)|(esk11_0!=k3_mcart_1(X42,X43,X44)|esk10_0=X44))))&(((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&esk9_0!=k1_xboole_0)&esk10_0!=k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((X19!=k7_mcart_1(X15,X16,X17,X18)|(X18!=k3_mcart_1(X20,X21,X22)|X19=X22)|~m1_subset_1(X19,X17)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&((X18=k3_mcart_1(esk1_5(X15,X16,X17,X18,X19),esk2_5(X15,X16,X17,X18,X19),esk3_5(X15,X16,X17,X18,X19))|X19=k7_mcart_1(X15,X16,X17,X18)|~m1_subset_1(X19,X17)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&(X19!=esk3_5(X15,X16,X17,X18,X19)|X19=k7_mcart_1(X15,X16,X17,X18)|~m1_subset_1(X19,X17)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_mcart_1])])])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.37  cnf(c_0_12, plain, (m1_subset_1(esk6_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, plain, (X1=X8|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=k7_mcart_1(X2,X3,X4,X5)|X5!=k3_mcart_1(X6,X7,X8)|~m1_subset_1(X1,X4)|~m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_16, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_17, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))|m1_subset_1(k7_mcart_1(X26,X27,X28,X29),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (esk10_0=X3|~m1_subset_1(X1,esk7_0)|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X3,esk9_0)|esk11_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_19, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk6_4(X1,X2,X3,X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(rw,[status(thm)],[c_0_14, c_0_13])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_24, plain, (m1_subset_1(esk5_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_25, plain, (X1=X8|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1!=k7_mcart_1(X2,X3,X4,X5)|X5!=k4_tarski(k4_tarski(X6,X7),X8)|~m1_subset_1(X1,X4)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_13])).
% 0.13/0.37  cnf(c_0_26, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_27, plain, (X1=k3_mcart_1(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (esk10_0=X3|esk11_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk9_0)|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X1,esk7_0)), inference(rw,[status(thm)],[c_0_18, c_0_16])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk6_4(esk7_0,esk8_0,esk9_0,esk11_0),esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.37  cnf(c_0_30, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk5_4(X1,X2,X3,X4),X2)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_24, c_0_13])).
% 0.13/0.37  cnf(c_0_31, plain, (m1_subset_1(esk4_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_32, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=X5|X4!=k7_mcart_1(X3,X2,X1,k4_tarski(k4_tarski(X6,X7),X5))|~m1_subset_1(k4_tarski(k4_tarski(X6,X7),X5),k2_zfmisc_1(k2_zfmisc_1(X3,X2),X1))|~m1_subset_1(X4,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_33, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_26, c_0_13])).
% 0.13/0.37  cnf(c_0_34, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_tarski(k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1)),esk6_4(X2,X3,X4,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_16]), c_0_13])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)=esk10_0|k4_tarski(k4_tarski(X1,X2),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))!=esk11_0|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X1,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.37  cnf(c_0_37, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk4_4(X1,X2,X3,X4),X1)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_31, c_0_13])).
% 0.13/0.37  cnf(c_0_38, plain, (k7_mcart_1(X1,X2,X3,k4_tarski(k4_tarski(X4,X5),X6))=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (k4_tarski(k4_tarski(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk5_4(esk7_0,esk8_0,esk9_0,esk11_0)),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))=esk11_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)=esk10_0|k4_tarski(k4_tarski(X1,esk5_4(esk7_0,esk8_0,esk9_0,esk11_0)),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))!=esk11_0|~m1_subset_1(X1,esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k7_mcart_1(X1,X2,X3,esk11_0)=esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_39])])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (k7_mcart_1(X1,X2,X3,esk11_0)=esk10_0|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (esk10_0!=k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_20]), c_0_45]), c_0_21]), c_0_22]), c_0_23]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 47
% 0.13/0.37  # Proof object clause steps            : 34
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 21
% 0.13/0.37  # Proof object clause conjectures      : 18
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 14
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 30
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 16
% 0.13/0.37  # Removed in clause preprocessing      : 2
% 0.13/0.37  # Initial clauses in saturation        : 14
% 0.13/0.37  # Processed clauses                    : 45
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 3
% 0.13/0.37  # ...remaining for further processing  : 41
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 8
% 0.13/0.37  # Generated clauses                    : 48
% 0.13/0.37  # ...of the previous two non-trivial   : 53
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 40
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 8
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
% 0.13/0.37  # Current number of processed clauses  : 33
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 5
% 0.13/0.37  #    Non-unit-clauses                  : 20
% 0.13/0.37  # Current number of unprocessed clauses: 19
% 0.13/0.37  # ...number of literals in the above   : 132
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 10
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 37
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.37  # Unit Clause-clause subsumption calls : 16
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2601
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.024 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.028 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
