%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 647 expanded)
%              Number of clauses        :   38 ( 250 expanded)
%              Number of leaves         :    7 ( 161 expanded)
%              Depth                    :   10
%              Number of atoms          :  274 (4044 expanded)
%              Number of equality atoms :  202 (2628 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

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

fof(t59_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ? [X6,X7,X8,X9] :
                ( X5 = k4_mcart_1(X6,X7,X8,X9)
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
                    & k9_mcart_1(X1,X2,X3,X4,X5) = X7
                    & k10_mcart_1(X1,X2,X3,X4,X5) = X8
                    & k11_mcart_1(X1,X2,X3,X4,X5) = X9 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20] : k4_mcart_1(X17,X18,X19,X20) = k4_tarski(k3_mcart_1(X17,X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13] : k3_mcart_1(X11,X12,X13) = k4_tarski(k4_tarski(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X21,X22,X23,X24] : k4_zfmisc_1(X21,X22,X23,X24) = k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] : k3_zfmisc_1(X14,X15,X16) = k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( m1_subset_1(esk1_6(X39,X40,X41,X42,X43,X44),X39)
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 = k8_mcart_1(X39,X40,X41,X42,X44)
        | ~ m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)) )
      & ( m1_subset_1(esk2_6(X39,X40,X41,X42,X43,X44),X40)
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 = k8_mcart_1(X39,X40,X41,X42,X44)
        | ~ m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)) )
      & ( m1_subset_1(esk3_6(X39,X40,X41,X42,X43,X44),X41)
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 = k8_mcart_1(X39,X40,X41,X42,X44)
        | ~ m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)) )
      & ( m1_subset_1(esk4_6(X39,X40,X41,X42,X43,X44),X42)
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 = k8_mcart_1(X39,X40,X41,X42,X44)
        | ~ m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)) )
      & ( X44 = k4_mcart_1(esk1_6(X39,X40,X41,X42,X43,X44),esk2_6(X39,X40,X41,X42,X43,X44),esk3_6(X39,X40,X41,X42,X43,X44),esk4_6(X39,X40,X41,X42,X43,X44))
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 = k8_mcart_1(X39,X40,X41,X42,X44)
        | ~ m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)) )
      & ( X43 != esk1_6(X39,X40,X41,X42,X43,X44)
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 = k8_mcart_1(X39,X40,X41,X42,X44)
        | ~ m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_mcart_1])])])])).

cnf(c_0_13,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,(
    ! [X55,X56,X57,X58] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X55,esk5_0)
        | ~ m1_subset_1(X56,esk6_0)
        | ~ m1_subset_1(X57,esk7_0)
        | ~ m1_subset_1(X58,esk8_0)
        | esk10_0 != k4_mcart_1(X55,X56,X57,X58)
        | esk9_0 = X56 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

cnf(c_0_18,plain,
    ( X1 = k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k8_mcart_1(X2,X3,X4,X5,X1)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( k8_mcart_1(X25,X26,X27,X28,X29) = X30
        | X29 != k4_mcart_1(X30,X31,X32,X33)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( k9_mcart_1(X25,X26,X27,X28,X29) = X31
        | X29 != k4_mcart_1(X30,X31,X32,X33)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( k10_mcart_1(X25,X26,X27,X28,X29) = X32
        | X29 != k4_mcart_1(X30,X31,X32,X33)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( k11_mcart_1(X25,X26,X27,X28,X29) = X33
        | X29 != k4_mcart_1(X30,X31,X32,X33)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_mcart_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( esk9_0 = X2
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X4,esk8_0)
    | esk10_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X6 = k8_mcart_1(X2,X3,X4,X5,X1)
    | X1 = k4_tarski(k4_tarski(k4_tarski(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1)),esk3_6(X2,X3,X4,X5,X6,X1)),esk4_6(X2,X3,X4,X5,X6,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_35,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_36,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_37,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k8_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_38,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X6,X8,X9)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( esk9_0 = X2
    | esk10_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ m1_subset_1(X4,esk8_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) = esk10_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_45,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k4_tarski(k4_tarski(X7,X6),X8),X9)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_19]),c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_47,plain,
    ( k9_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk9_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) = esk10_0
    | X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k9_mcart_1(X2,X3,X4,X5,esk10_0) = esk9_0
    | X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk9_0 != k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_50]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.047 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.19/0.40  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.40  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.19/0.40  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.40  fof(t80_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X8)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k9_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_mcart_1)).
% 0.19/0.41  fof(t79_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_mcart_1)).
% 0.19/0.41  fof(t59_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 0.19/0.41  fof(c_0_7, plain, ![X17, X18, X19, X20]:k4_mcart_1(X17,X18,X19,X20)=k4_tarski(k3_mcart_1(X17,X18,X19),X20), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.19/0.41  fof(c_0_8, plain, ![X11, X12, X13]:k3_mcart_1(X11,X12,X13)=k4_tarski(k4_tarski(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.41  fof(c_0_9, plain, ![X21, X22, X23, X24]:k4_zfmisc_1(X21,X22,X23,X24)=k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.19/0.41  fof(c_0_10, plain, ![X14, X15, X16]:k3_zfmisc_1(X14,X15,X16)=k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.41  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X8)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k9_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t80_mcart_1])).
% 0.19/0.41  fof(c_0_12, plain, ![X39, X40, X41, X42, X43, X44]:((m1_subset_1(esk1_6(X39,X40,X41,X42,X43,X44),X39)|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0|X43=k8_mcart_1(X39,X40,X41,X42,X44))|~m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)))&((m1_subset_1(esk2_6(X39,X40,X41,X42,X43,X44),X40)|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0|X43=k8_mcart_1(X39,X40,X41,X42,X44))|~m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)))&((m1_subset_1(esk3_6(X39,X40,X41,X42,X43,X44),X41)|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0|X43=k8_mcart_1(X39,X40,X41,X42,X44))|~m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)))&((m1_subset_1(esk4_6(X39,X40,X41,X42,X43,X44),X42)|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0|X43=k8_mcart_1(X39,X40,X41,X42,X44))|~m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)))&((X44=k4_mcart_1(esk1_6(X39,X40,X41,X42,X43,X44),esk2_6(X39,X40,X41,X42,X43,X44),esk3_6(X39,X40,X41,X42,X43,X44),esk4_6(X39,X40,X41,X42,X43,X44))|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0|X43=k8_mcart_1(X39,X40,X41,X42,X44))|~m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)))&(X43!=esk1_6(X39,X40,X41,X42,X43,X44)|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0|X43=k8_mcart_1(X39,X40,X41,X42,X44))|~m1_subset_1(X44,k4_zfmisc_1(X39,X40,X41,X42)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_mcart_1])])])])).
% 0.19/0.41  cnf(c_0_13, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_14, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_15, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_16, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  fof(c_0_17, negated_conjecture, ![X55, X56, X57, X58]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X55,esk5_0)|(~m1_subset_1(X56,esk6_0)|(~m1_subset_1(X57,esk7_0)|(~m1_subset_1(X58,esk8_0)|(esk10_0!=k4_mcart_1(X55,X56,X57,X58)|esk9_0=X56)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.19/0.41  cnf(c_0_18, plain, (X1=k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X6=k8_mcart_1(X2,X3,X4,X5,X1)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_19, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.41  cnf(c_0_20, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_22, plain, (m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_23, plain, (m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_24, plain, (m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_25, plain, (m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_26, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33]:((((k8_mcart_1(X25,X26,X27,X28,X29)=X30|X29!=k4_mcart_1(X30,X31,X32,X33)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))&(k9_mcart_1(X25,X26,X27,X28,X29)=X31|X29!=k4_mcart_1(X30,X31,X32,X33)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0)))&(k10_mcart_1(X25,X26,X27,X28,X29)=X32|X29!=k4_mcart_1(X30,X31,X32,X33)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0)))&(k11_mcart_1(X25,X26,X27,X28,X29)=X33|X29!=k4_mcart_1(X30,X31,X32,X33)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_mcart_1])])])])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (esk9_0=X2|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_28, plain, (X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X6=k8_mcart_1(X2,X3,X4,X5,X1)|X1=k4_tarski(k4_tarski(k4_tarski(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1)),esk3_6(X2,X3,X4,X5,X6,X1)),esk4_6(X2,X3,X4,X5,X6,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_34, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.41  cnf(c_0_35, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_23, c_0_20])).
% 0.19/0.41  cnf(c_0_36, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_24, c_0_20])).
% 0.19/0.41  cnf(c_0_37, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|~m1_subset_1(X6,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_25, c_0_20])).
% 0.19/0.41  cnf(c_0_38, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X6,X8,X9)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (esk9_0=X2|esk10_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~m1_subset_1(X4,esk8_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(rw,[status(thm)],[c_0_27, c_0_19])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))=esk10_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_45, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k9_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k4_tarski(k4_tarski(X7,X6),X8),X9)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_19]), c_0_20])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.41  cnf(c_0_47, plain, (k9_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8))=X6|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk9_0),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))=esk10_0|X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_40, c_0_46])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k9_mcart_1(X2,X3,X4,X5,esk10_0)=esk9_0|X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|~m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (esk9_0!=k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (X1=k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_50]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_51]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 53
% 0.19/0.41  # Proof object clause steps            : 38
% 0.19/0.41  # Proof object formula steps           : 15
% 0.19/0.41  # Proof object conjectures             : 22
% 0.19/0.41  # Proof object clause conjectures      : 19
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 17
% 0.19/0.41  # Proof object initial formulas used   : 7
% 0.19/0.41  # Proof object generating inferences   : 9
% 0.19/0.41  # Proof object simplifying inferences  : 44
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 8
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 25
% 0.19/0.41  # Removed in clause preprocessing      : 4
% 0.19/0.41  # Initial clauses in saturation        : 21
% 0.19/0.41  # Processed clauses                    : 63
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 0
% 0.19/0.41  # ...remaining for further processing  : 63
% 0.19/0.41  # Other redundant clauses eliminated   : 4
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 32
% 0.19/0.41  # Generated clauses                    : 129
% 0.19/0.41  # ...of the previous two non-trivial   : 131
% 0.19/0.41  # Contextual simplify-reflections      : 5
% 0.19/0.41  # Paramodulations                      : 125
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 4
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 6
% 0.19/0.41  #    Positive orientable unit clauses  : 1
% 0.19/0.41  #    Positive unorientable unit clauses: 1
% 0.19/0.41  #    Negative unit clauses             : 4
% 0.19/0.41  #    Non-unit-clauses                  : 0
% 0.19/0.41  # Current number of unprocessed clauses: 79
% 0.19/0.41  # ...number of literals in the above   : 555
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 57
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 112
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 26
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 5
% 0.19/0.41  # Unit Clause-clause subsumption calls : 11
% 0.19/0.41  # Rewrite failures with RHS unbound    : 3
% 0.19/0.41  # BW rewrite match attempts            : 79
% 0.19/0.41  # BW rewrite match successes           : 76
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 5405
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.056 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.062 s
% 0.19/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
