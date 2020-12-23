%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:18 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 237 expanded)
%              Number of clauses        :   31 (  87 expanded)
%              Number of leaves         :    5 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 (1427 expanded)
%              Number of equality atoms :  141 ( 905 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15] :
      ( ( m1_subset_1(esk1_4(X12,X13,X14,X15),X12)
        | ~ m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( m1_subset_1(esk2_4(X12,X13,X14,X15),X13)
        | ~ m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( m1_subset_1(esk3_4(X12,X13,X14,X15),X14)
        | ~ m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X15 = k3_mcart_1(esk1_4(X12,X13,X14,X15),esk2_4(X12,X13,X14,X15),esk3_4(X12,X13,X14,X15))
        | ~ m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] : k3_zfmisc_1(X9,X10,X11) = k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_8,negated_conjecture,(
    ! [X35,X36,X37] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X35,esk4_0)
        | ~ m1_subset_1(X36,esk5_0)
        | ~ m1_subset_1(X37,esk6_0)
        | esk8_0 != k3_mcart_1(X35,X36,X37)
        | esk7_0 = X37 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( X1 = k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_15,plain,(
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

cnf(c_0_16,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk3_4(X1,X2,X3,X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_22,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_23,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_10])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22] :
      ( ( k5_mcart_1(X19,X20,X21,X22) = k1_mcart_1(k1_mcart_1(X22))
        | ~ m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( k6_mcart_1(X19,X20,X21,X22) = k2_mcart_1(k1_mcart_1(X22))
        | ~ m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( k7_mcart_1(X19,X20,X21,X22) = k2_mcart_1(X22)
        | ~ m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_25,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = X5
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k3_mcart_1(X6,X7,X5)
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( esk7_0 = X3
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( k3_mcart_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_31,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = X5
    | X4 != k3_mcart_1(X6,X7,X5)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( esk3_4(esk4_0,esk5_0,esk6_0,esk8_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_34,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_10])).

cnf(c_0_35,plain,
    ( k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k3_mcart_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk7_0) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( esk7_0 != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk8_0) = esk7_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k2_mcart_1(esk8_0) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_17]),c_0_38]),c_0_40]),c_0_18]),c_0_19]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.029 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.13/0.37  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(t68_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 0.13/0.37  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.13/0.37  fof(c_0_6, plain, ![X12, X13, X14, X15]:((m1_subset_1(esk1_4(X12,X13,X14,X15),X12)|~m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))|(X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&((m1_subset_1(esk2_4(X12,X13,X14,X15),X13)|~m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))|(X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&((m1_subset_1(esk3_4(X12,X13,X14,X15),X14)|~m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))|(X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&(X15=k3_mcart_1(esk1_4(X12,X13,X14,X15),esk2_4(X12,X13,X14,X15),esk3_4(X12,X13,X14,X15))|~m1_subset_1(X15,k3_zfmisc_1(X12,X13,X14))|(X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X9, X10, X11]:k3_zfmisc_1(X9,X10,X11)=k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ![X35, X36, X37]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X35,esk4_0)|(~m1_subset_1(X36,esk5_0)|(~m1_subset_1(X37,esk6_0)|(esk8_0!=k3_mcart_1(X35,X36,X37)|esk7_0=X37))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (X1=k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_13, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_14, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_15, plain, ![X23, X24, X25, X26, X27, X28, X29]:(((k5_mcart_1(X23,X24,X25,X26)=X27|X26!=k3_mcart_1(X27,X28,X29)|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25)))&(k6_mcart_1(X23,X24,X25,X26)=X28|X26!=k3_mcart_1(X27,X28,X29)|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))))&(k7_mcart_1(X23,X24,X25,X26)=X29|X26!=k3_mcart_1(X27,X28,X29)|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_mcart_1])])])])).
% 0.13/0.37  cnf(c_0_16, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_11, c_0_10])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_21, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk3_4(X1,X2,X3,X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_12, c_0_10])).
% 0.13/0.37  cnf(c_0_22, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_13, c_0_10])).
% 0.13/0.37  cnf(c_0_23, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_14, c_0_10])).
% 0.13/0.37  fof(c_0_24, plain, ![X19, X20, X21, X22]:(((k5_mcart_1(X19,X20,X21,X22)=k1_mcart_1(k1_mcart_1(X22))|~m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0))&(k6_mcart_1(X19,X20,X21,X22)=k2_mcart_1(k1_mcart_1(X22))|~m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0)))&(k7_mcart_1(X19,X20,X21,X22)=k2_mcart_1(X22)|~m1_subset_1(X22,k3_zfmisc_1(X19,X20,X21))|(X19=k1_xboole_0|X20=k1_xboole_0|X21=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.13/0.37  cnf(c_0_25, plain, (k7_mcart_1(X1,X2,X3,X4)=X5|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k3_mcart_1(X6,X7,X5)|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (esk7_0=X3|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k3_mcart_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.37  cnf(c_0_31, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_32, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=X5|X4!=k3_mcart_1(X6,X7,X5)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_25, c_0_10])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.13/0.37  cnf(c_0_34, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_31, c_0_10])).
% 0.13/0.37  cnf(c_0_35, plain, (k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X6|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (k3_mcart_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk7_0)=esk8_0), inference(rw,[status(thm)],[c_0_27, c_0_33])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (esk7_0!=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (k7_mcart_1(X1,X2,X3,esk8_0)=esk7_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (k2_mcart_1(esk8_0)!=esk7_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_17]), c_0_38]), c_0_40]), c_0_18]), c_0_19]), c_0_20]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 42
% 0.13/0.37  # Proof object clause steps            : 31
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 20
% 0.13/0.37  # Proof object clause conjectures      : 17
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 8
% 0.13/0.37  # Proof object simplifying inferences  : 34
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 17
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 16
% 0.13/0.37  # Processed clauses                    : 47
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 47
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 18
% 0.13/0.38  # ...of the previous two non-trivial   : 20
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 15
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 25
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 12
% 0.13/0.38  # Current number of unprocessed clauses: 5
% 0.13/0.38  # ...number of literals in the above   : 25
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 20
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 33
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 51
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1982
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
