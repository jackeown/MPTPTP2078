%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:31 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 260 expanded)
%              Number of clauses        :   33 (  82 expanded)
%              Number of leaves         :    5 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  224 (2385 expanded)
%              Number of equality atoms :  160 (1465 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   30 (   3 average)
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

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(t33_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

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
                           => X5 = X10 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k11_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t82_mcart_1])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( m1_subset_1(esk1_5(X11,X12,X13,X14,X15),X11)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( m1_subset_1(esk2_5(X11,X12,X13,X14,X15),X12)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( m1_subset_1(esk3_5(X11,X12,X13,X14,X15),X13)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( m1_subset_1(esk4_5(X11,X12,X13,X14,X15),X14)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X15 = k4_mcart_1(esk1_5(X11,X12,X13,X14,X15),esk2_5(X11,X12,X13,X14,X15),esk3_5(X11,X12,X13,X14,X15),esk4_5(X11,X12,X13,X14,X15))
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X44,X45,X46,X47] :
      ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X44,esk5_0)
        | ~ m1_subset_1(X45,esk6_0)
        | ~ m1_subset_1(X46,esk7_0)
        | ~ m1_subset_1(X47,esk8_0)
        | esk10_0 != k4_mcart_1(X44,X45,X46,X47)
        | esk9_0 = X47 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( esk9_0 = X4
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X4,esk8_0)
    | esk10_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( esk9_0 = X1
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X2,X3,X1) != esk10_0
    | ~ m1_subset_1(X1,esk8_0)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_20,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( k8_mcart_1(X33,X34,X35,X36,X37) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X37)))
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( k9_mcart_1(X33,X34,X35,X36,X37) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X37)))
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( k10_mcart_1(X33,X34,X35,X36,X37) = k2_mcart_1(k1_mcart_1(X37))
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( k11_mcart_1(X33,X34,X35,X36,X37) = k2_mcart_1(X37)
        | ~ m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_21,negated_conjecture,
    ( esk9_0 = X1
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X2,X1) != esk10_0
    | ~ m1_subset_1(X1,esk8_0)
    | ~ m1_subset_1(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_24,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( X28 = k1_xboole_0
      | X29 = k1_xboole_0
      | X30 = k1_xboole_0
      | X31 = k1_xboole_0
      | ~ m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31))
      | X32 = k4_mcart_1(k8_mcart_1(X28,X29,X30,X31,X32),k9_mcart_1(X28,X29,X30,X31,X32),k10_mcart_1(X28,X29,X30,X31,X32),k11_mcart_1(X28,X29,X30,X31,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_25,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( esk9_0 = X1
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X1) != esk10_0
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_29,plain,
    ( X1 = k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_30,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( X20 = X24
        | k4_mcart_1(X20,X21,X22,X23) != k4_mcart_1(X24,X25,X26,X27) )
      & ( X21 = X25
        | k4_mcart_1(X20,X21,X22,X23) != k4_mcart_1(X24,X25,X26,X27) )
      & ( X22 = X26
        | k4_mcart_1(X20,X21,X22,X23) != k4_mcart_1(X24,X25,X26,X27) )
      & ( X23 = X27
        | k4_mcart_1(X20,X21,X22,X23) != k4_mcart_1(X24,X25,X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_mcart_1])])])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = k2_mcart_1(k1_mcart_1(esk10_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = k2_mcart_1(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = esk9_0
    | k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)) = esk10_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_36,plain,
    ( X1 = X2
    | k4_mcart_1(X3,X4,X5,X1) != k4_mcart_1(X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),k2_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(esk10_0)) = esk10_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_9]),c_0_32]),c_0_33]),c_0_10]),c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( esk9_0 != k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( k2_mcart_1(esk10_0) = X1
    | k4_mcart_1(X2,X3,X4,X1) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk9_0) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k2_mcart_1(esk10_0) != esk9_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.13/0.37  # and selection function SelectNegativeLiterals.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.021 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t82_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X10)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k11_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_mcart_1)).
% 0.13/0.37  fof(l68_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>![X9]:(m1_subset_1(X9,X4)=>X5!=k4_mcart_1(X6,X7,X8,X9)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 0.13/0.37  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.13/0.37  fof(t60_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 0.13/0.37  fof(t33_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X10)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k11_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t82_mcart_1])).
% 0.13/0.37  fof(c_0_6, plain, ![X11, X12, X13, X14, X15]:((m1_subset_1(esk1_5(X11,X12,X13,X14,X15),X11)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&((m1_subset_1(esk2_5(X11,X12,X13,X14,X15),X12)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&((m1_subset_1(esk3_5(X11,X12,X13,X14,X15),X13)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&((m1_subset_1(esk4_5(X11,X12,X13,X14,X15),X14)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&(X15=k4_mcart_1(esk1_5(X11,X12,X13,X14,X15),esk2_5(X11,X12,X13,X14,X15),esk3_5(X11,X12,X13,X14,X15),esk4_5(X11,X12,X13,X14,X15))|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ![X44, X45, X46, X47]:(m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X44,esk5_0)|(~m1_subset_1(X45,esk6_0)|(~m1_subset_1(X46,esk7_0)|(~m1_subset_1(X47,esk8_0)|(esk10_0!=k4_mcart_1(X44,X45,X46,X47)|esk9_0=X47)))))&((((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  cnf(c_0_8, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk10_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (esk9_0=X4|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X4,esk8_0)|esk10_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_16, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (esk9_0=X1|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X2,X3,X1)!=esk10_0|~m1_subset_1(X1,esk8_0)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X2,esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_20, plain, ![X33, X34, X35, X36, X37]:((((k8_mcart_1(X33,X34,X35,X36,X37)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X37)))|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0))&(k9_mcart_1(X33,X34,X35,X36,X37)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X37)))|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0)))&(k10_mcart_1(X33,X34,X35,X36,X37)=k2_mcart_1(k1_mcart_1(X37))|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0)))&(k11_mcart_1(X33,X34,X35,X36,X37)=k2_mcart_1(X37)|~m1_subset_1(X37,k4_zfmisc_1(X33,X34,X35,X36))|(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|X36=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (esk9_0=X1|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X2,X1)!=esk10_0|~m1_subset_1(X1,esk8_0)|~m1_subset_1(X2,esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_23, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_24, plain, ![X28, X29, X30, X31, X32]:(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|(~m1_subset_1(X32,k4_zfmisc_1(X28,X29,X30,X31))|X32=k4_mcart_1(k8_mcart_1(X28,X29,X30,X31,X32),k9_mcart_1(X28,X29,X30,X31,X32),k10_mcart_1(X28,X29,X30,X31,X32),k11_mcart_1(X28,X29,X30,X31,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).
% 0.13/0.37  cnf(c_0_25, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_26, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (esk9_0=X1|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),X1)!=esk10_0|~m1_subset_1(X1,esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_29, plain, (X1=k4_mcart_1(esk1_5(X2,X3,X4,X5,X1),esk2_5(X2,X3,X4,X5,X1),esk3_5(X2,X3,X4,X5,X1),esk4_5(X2,X3,X4,X5,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_30, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((X20=X24|k4_mcart_1(X20,X21,X22,X23)!=k4_mcart_1(X24,X25,X26,X27))&(X21=X25|k4_mcart_1(X20,X21,X22,X23)!=k4_mcart_1(X24,X25,X26,X27)))&(X22=X26|k4_mcart_1(X20,X21,X22,X23)!=k4_mcart_1(X24,X25,X26,X27)))&(X23=X27|k4_mcart_1(X20,X21,X22,X23)!=k4_mcart_1(X24,X25,X26,X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_mcart_1])])])).
% 0.13/0.37  cnf(c_0_31, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=k2_mcart_1(k1_mcart_1(esk10_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=k2_mcart_1(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=esk9_0|k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))!=esk10_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0))=esk10_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_36, plain, (X1=X2|k4_mcart_1(X3,X4,X5,X1)!=k4_mcart_1(X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k4_mcart_1(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),k2_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(esk10_0))=esk10_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_9]), c_0_32]), c_0_33]), c_0_10]), c_0_11]), c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (esk4_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (esk9_0!=k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (k2_mcart_1(esk10_0)=X1|k4_mcart_1(X2,X3,X4,X1)!=esk10_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (k4_mcart_1(esk1_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk2_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk3_5(esk5_0,esk6_0,esk7_0,esk8_0,esk10_0),esk9_0)=esk10_0), inference(rw,[status(thm)],[c_0_35, c_0_38])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k2_mcart_1(esk10_0)!=esk9_0), inference(rw,[status(thm)],[c_0_39, c_0_33])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 44
% 0.13/0.37  # Proof object clause steps            : 33
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 27
% 0.13/0.37  # Proof object clause conjectures      : 24
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 16
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 14
% 0.13/0.37  # Proof object simplifying inferences  : 39
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 21
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 21
% 0.13/0.37  # Processed clauses                    : 96
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 21
% 0.13/0.37  # ...remaining for further processing  : 75
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 11
% 0.13/0.37  # Generated clauses                    : 78
% 0.13/0.37  # ...of the previous two non-trivial   : 76
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 74
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 4
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
% 0.13/0.37  # Current number of processed clauses  : 43
% 0.13/0.37  #    Positive orientable unit clauses  : 12
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 5
% 0.13/0.37  #    Non-unit-clauses                  : 26
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 32
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 79
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 47
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 21
% 0.13/0.37  # Unit Clause-clause subsumption calls : 6
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 10
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3993
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.023 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.028 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
