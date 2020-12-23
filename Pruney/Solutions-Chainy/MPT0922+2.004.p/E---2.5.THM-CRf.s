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
% DateTime   : Thu Dec  3 11:00:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 698 expanded)
%              Number of clauses        :   40 ( 252 expanded)
%              Number of leaves         :    7 ( 173 expanded)
%              Depth                    :   10
%              Number of atoms          :  317 (5125 expanded)
%              Number of equality atoms :  238 (3289 expanded)
%              Maximal formula depth    :   21 (   7 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).

fof(t81_mcart_1,axiom,(
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

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17] : k4_mcart_1(X14,X15,X16,X17) = k4_tarski(k3_mcart_1(X14,X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13] : k3_mcart_1(X11,X12,X13) = k4_tarski(k4_tarski(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( m1_subset_1(esk1_6(X36,X37,X38,X39,X40,X41),X36)
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k10_mcart_1(X36,X37,X38,X39,X41)
        | ~ m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)) )
      & ( m1_subset_1(esk2_6(X36,X37,X38,X39,X40,X41),X37)
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k10_mcart_1(X36,X37,X38,X39,X41)
        | ~ m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)) )
      & ( m1_subset_1(esk3_6(X36,X37,X38,X39,X40,X41),X38)
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k10_mcart_1(X36,X37,X38,X39,X41)
        | ~ m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)) )
      & ( m1_subset_1(esk4_6(X36,X37,X38,X39,X40,X41),X39)
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k10_mcart_1(X36,X37,X38,X39,X41)
        | ~ m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)) )
      & ( X41 = k4_mcart_1(esk1_6(X36,X37,X38,X39,X40,X41),esk2_6(X36,X37,X38,X39,X40,X41),esk3_6(X36,X37,X38,X39,X40,X41),esk4_6(X36,X37,X38,X39,X40,X41))
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k10_mcart_1(X36,X37,X38,X39,X41)
        | ~ m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)) )
      & ( X40 != esk3_6(X36,X37,X38,X39,X40,X41)
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k10_mcart_1(X36,X37,X38,X39,X41)
        | ~ m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_mcart_1])])])])).

cnf(c_0_11,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21] : k4_zfmisc_1(X18,X19,X20,X21) = k2_zfmisc_1(k3_zfmisc_1(X18,X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_14,negated_conjecture,(
    ! [X52,X53,X54,X55] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X52,esk5_0)
        | ~ m1_subset_1(X53,esk6_0)
        | ~ m1_subset_1(X54,esk7_0)
        | ~ m1_subset_1(X55,esk8_0)
        | esk10_0 != k4_mcart_1(X52,X53,X54,X55)
        | esk9_0 = X55 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_15,plain,
    ( X1 = k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k10_mcart_1(X2,X3,X4,X5,X1)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34,X35] :
      ( ( k8_mcart_1(X27,X28,X29,X30,X31) = X32
        | X31 != k4_mcart_1(X32,X33,X34,X35)
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30)) )
      & ( k9_mcart_1(X27,X28,X29,X30,X31) = X33
        | X31 != k4_mcart_1(X32,X33,X34,X35)
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30)) )
      & ( k10_mcart_1(X27,X28,X29,X30,X31) = X34
        | X31 != k4_mcart_1(X32,X33,X34,X35)
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30)) )
      & ( k11_mcart_1(X27,X28,X29,X30,X31) = X35
        | X31 != k4_mcart_1(X32,X33,X34,X35)
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).

cnf(c_0_24,negated_conjecture,
    ( esk9_0 = X4
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X4,esk8_0)
    | esk10_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X6 = k10_mcart_1(X2,X3,X4,X5,X1)
    | X1 = k4_tarski(k4_tarski(k4_tarski(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1)),esk3_6(X2,X3,X4,X5,X6,X1)),esk4_6(X2,X3,X4,X5,X6,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_32,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_33,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_34,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k10_mcart_1(X1,X2,X3,X4,X6)
    | m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)
    | ~ m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

fof(c_0_35,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( k8_mcart_1(X22,X23,X24,X25,X26) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X26)))
        | ~ m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( k9_mcart_1(X22,X23,X24,X25,X26) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X26)))
        | ~ m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( k10_mcart_1(X22,X23,X24,X25,X26) = k2_mcart_1(k1_mcart_1(X26))
        | ~ m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( k11_mcart_1(X22,X23,X24,X25,X26) = k2_mcart_1(X26)
        | ~ m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_36,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = X6
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 != k4_mcart_1(X7,X8,X9,X6)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( esk9_0 = X4
    | esk10_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ m1_subset_1(X4,esk8_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)) = esk10_0
    | X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_43,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = X6
    | X5 != k4_tarski(k4_tarski(k4_tarski(X7,X8),X9),X6)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_16]),c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0) = esk9_0
    | X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_46,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_17])).

cnf(c_0_47,plain,
    ( k11_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk9_0) = esk10_0
    | X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( esk9_0 != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = k2_mcart_1(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)
    | k11_mcart_1(X2,X3,X4,X5,esk10_0) = esk9_0
    | X5 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_mcart_1(esk10_0) != esk9_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_50]),c_0_52]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.053 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.20/0.41  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.41  fof(t82_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X10)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k11_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_mcart_1)).
% 0.20/0.41  fof(t81_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X9)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 0.20/0.41  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.20/0.41  fof(t78_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 0.20/0.41  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.20/0.41  fof(c_0_7, plain, ![X14, X15, X16, X17]:k4_mcart_1(X14,X15,X16,X17)=k4_tarski(k3_mcart_1(X14,X15,X16),X17), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.20/0.41  fof(c_0_8, plain, ![X11, X12, X13]:k3_mcart_1(X11,X12,X13)=k4_tarski(k4_tarski(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.41  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X10)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k11_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t82_mcart_1])).
% 0.20/0.41  fof(c_0_10, plain, ![X36, X37, X38, X39, X40, X41]:((m1_subset_1(esk1_6(X36,X37,X38,X39,X40,X41),X36)|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0|X40=k10_mcart_1(X36,X37,X38,X39,X41))|~m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)))&((m1_subset_1(esk2_6(X36,X37,X38,X39,X40,X41),X37)|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0|X40=k10_mcart_1(X36,X37,X38,X39,X41))|~m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)))&((m1_subset_1(esk3_6(X36,X37,X38,X39,X40,X41),X38)|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0|X40=k10_mcart_1(X36,X37,X38,X39,X41))|~m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)))&((m1_subset_1(esk4_6(X36,X37,X38,X39,X40,X41),X39)|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0|X40=k10_mcart_1(X36,X37,X38,X39,X41))|~m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)))&((X41=k4_mcart_1(esk1_6(X36,X37,X38,X39,X40,X41),esk2_6(X36,X37,X38,X39,X40,X41),esk3_6(X36,X37,X38,X39,X40,X41),esk4_6(X36,X37,X38,X39,X40,X41))|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0|X40=k10_mcart_1(X36,X37,X38,X39,X41))|~m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)))&(X40!=esk3_6(X36,X37,X38,X39,X40,X41)|(X36=k1_xboole_0|X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0|X40=k10_mcart_1(X36,X37,X38,X39,X41))|~m1_subset_1(X41,k4_zfmisc_1(X36,X37,X38,X39)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_mcart_1])])])])).
% 0.20/0.41  cnf(c_0_11, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_12, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  fof(c_0_13, plain, ![X18, X19, X20, X21]:k4_zfmisc_1(X18,X19,X20,X21)=k2_zfmisc_1(k3_zfmisc_1(X18,X19,X20),X21), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ![X52, X53, X54, X55]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X52,esk5_0)|(~m1_subset_1(X53,esk6_0)|(~m1_subset_1(X54,esk7_0)|(~m1_subset_1(X55,esk8_0)|(esk10_0!=k4_mcart_1(X52,X53,X54,X55)|esk9_0=X55)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.20/0.41  cnf(c_0_15, plain, (X1=k4_mcart_1(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1),esk3_6(X2,X3,X4,X5,X6,X1),esk4_6(X2,X3,X4,X5,X6,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X6=k10_mcart_1(X2,X3,X4,X5,X1)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_16, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.41  cnf(c_0_17, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_19, plain, (m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_20, plain, (m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_21, plain, (m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_22, plain, (m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|~m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  fof(c_0_23, plain, ![X27, X28, X29, X30, X31, X32, X33, X34, X35]:((((k8_mcart_1(X27,X28,X29,X30,X31)=X32|X31!=k4_mcart_1(X32,X33,X34,X35)|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0)|~m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30)))&(k9_mcart_1(X27,X28,X29,X30,X31)=X33|X31!=k4_mcart_1(X32,X33,X34,X35)|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0)|~m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30))))&(k10_mcart_1(X27,X28,X29,X30,X31)=X34|X31!=k4_mcart_1(X32,X33,X34,X35)|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0)|~m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30))))&(k11_mcart_1(X27,X28,X29,X30,X31)=X35|X31!=k4_mcart_1(X32,X33,X34,X35)|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0)|~m1_subset_1(X31,k4_zfmisc_1(X27,X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_mcart_1])])])])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (esk9_0=X4|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_25, plain, (X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X6=k10_mcart_1(X2,X3,X4,X5,X1)|X1=k4_tarski(k4_tarski(k4_tarski(esk1_6(X2,X3,X4,X5,X6,X1),esk2_6(X2,X3,X4,X5,X6,X1)),esk3_6(X2,X3,X4,X5,X6,X1)),esk4_6(X2,X3,X4,X5,X6,X1))|~m1_subset_1(X1,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(esk5_0,esk6_0,esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_31, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),X1)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.20/0.41  cnf(c_0_32, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk2_6(X1,X2,X3,X4,X5,X6),X2)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_20, c_0_17])).
% 0.20/0.41  cnf(c_0_33, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk3_6(X1,X2,X3,X4,X5,X6),X3)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.20/0.41  cnf(c_0_34, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k10_mcart_1(X1,X2,X3,X4,X6)|m1_subset_1(esk4_6(X1,X2,X3,X4,X5,X6),X4)|~m1_subset_1(X6,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 0.20/0.41  fof(c_0_35, plain, ![X22, X23, X24, X25, X26]:((((k8_mcart_1(X22,X23,X24,X25,X26)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X26)))|~m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))|(X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0))&(k9_mcart_1(X22,X23,X24,X25,X26)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X26)))|~m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))|(X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)))&(k10_mcart_1(X22,X23,X24,X25,X26)=k2_mcart_1(k1_mcart_1(X26))|~m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))|(X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)))&(k11_mcart_1(X22,X23,X24,X25,X26)=k2_mcart_1(X26)|~m1_subset_1(X26,k4_zfmisc_1(X22,X23,X24,X25))|(X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.20/0.41  cnf(c_0_36, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=X6|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5!=k4_mcart_1(X7,X8,X9,X6)|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (esk9_0=X4|esk10_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~m1_subset_1(X4,esk8_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(rw,[status(thm)],[c_0_24, c_0_16])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0))=esk10_0|X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|m1_subset_1(esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.41  cnf(c_0_43, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_44, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k11_mcart_1(X1,X2,X3,X4,X5)=X6|X5!=k4_tarski(k4_tarski(k4_tarski(X7,X8),X9),X6)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_16]), c_0_17])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (esk4_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)=esk9_0|X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.41  cnf(c_0_46, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(rw,[status(thm)],[c_0_43, c_0_17])).
% 0.20/0.41  cnf(c_0_47, plain, (k11_mcart_1(X1,X2,X3,X4,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8))=X8|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0),esk2_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk3_6(esk5_0,esk6_0,esk7_0,esk8_0,X1,esk10_0)),esk9_0)=esk10_0|X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_38, c_0_45])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (esk9_0!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=k2_mcart_1(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)|k11_mcart_1(X2,X3,X4,X5,esk10_0)=esk9_0|X5=k1_xboole_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|~m1_subset_1(esk10_0,k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (k2_mcart_1(esk10_0)!=esk9_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (X1=k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_50]), c_0_52]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 55
% 0.20/0.41  # Proof object clause steps            : 40
% 0.20/0.41  # Proof object formula steps           : 15
% 0.20/0.41  # Proof object conjectures             : 24
% 0.20/0.41  # Proof object clause conjectures      : 21
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 17
% 0.20/0.41  # Proof object initial formulas used   : 7
% 0.20/0.41  # Proof object generating inferences   : 10
% 0.20/0.41  # Proof object simplifying inferences  : 50
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 7
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 24
% 0.20/0.41  # Removed in clause preprocessing      : 3
% 0.20/0.41  # Initial clauses in saturation        : 21
% 0.20/0.41  # Processed clauses                    : 64
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 0
% 0.20/0.41  # ...remaining for further processing  : 64
% 0.20/0.41  # Other redundant clauses eliminated   : 4
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 33
% 0.20/0.41  # Generated clauses                    : 114
% 0.20/0.41  # ...of the previous two non-trivial   : 117
% 0.20/0.41  # Contextual simplify-reflections      : 5
% 0.20/0.41  # Paramodulations                      : 110
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 4
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 6
% 0.20/0.41  #    Positive orientable unit clauses  : 1
% 0.20/0.41  #    Positive unorientable unit clauses: 1
% 0.20/0.41  #    Negative unit clauses             : 4
% 0.20/0.41  #    Non-unit-clauses                  : 0
% 0.20/0.41  # Current number of unprocessed clauses: 61
% 0.20/0.41  # ...number of literals in the above   : 422
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 57
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 104
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 25
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 5
% 0.20/0.41  # Unit Clause-clause subsumption calls : 6
% 0.20/0.41  # Rewrite failures with RHS unbound    : 3
% 0.20/0.41  # BW rewrite match attempts            : 73
% 0.20/0.41  # BW rewrite match successes           : 70
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 4959
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.059 s
% 0.20/0.41  # System time              : 0.009 s
% 0.20/0.41  # Total time               : 0.068 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
