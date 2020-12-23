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
% DateTime   : Thu Dec  3 11:00:18 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 354 expanded)
%              Number of clauses        :   34 ( 134 expanded)
%              Number of leaves         :    6 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 (1821 expanded)
%              Number of equality atoms :  115 (1173 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
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

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(t28_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

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
    ! [X28,X29,X30,X31] :
      ( X28 = k1_xboole_0
      | X29 = k1_xboole_0
      | X30 = k1_xboole_0
      | ~ m1_subset_1(X31,k3_zfmisc_1(X28,X29,X30))
      | X31 = k3_mcart_1(k5_mcart_1(X28,X29,X30,X31),k6_mcart_1(X28,X29,X30,X31),k7_mcart_1(X28,X29,X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,negated_conjecture,(
    ! [X37,X38,X39] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X37,esk4_0)
        | ~ m1_subset_1(X38,esk5_0)
        | ~ m1_subset_1(X39,esk6_0)
        | esk8_0 != k3_mcart_1(X37,X38,X39)
        | esk7_0 = X39 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17,X18] :
      ( ( m1_subset_1(esk1_4(X15,X16,X17,X18),X15)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( m1_subset_1(esk2_4(X15,X16,X17,X18),X16)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( m1_subset_1(esk3_4(X15,X16,X17,X18),X17)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X18 = k3_mcart_1(esk1_4(X15,X16,X17,X18),esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_12,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( X22 = X25
        | k3_mcart_1(X22,X23,X24) != k3_mcart_1(X25,X26,X27) )
      & ( X23 = X26
        | k3_mcart_1(X22,X23,X24) != k3_mcart_1(X25,X26,X27) )
      & ( X24 = X27
        | k3_mcart_1(X22,X23,X24) != k3_mcart_1(X25,X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = X2
    | k3_mcart_1(X3,X4,X1) != k3_mcart_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( X1 = k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( esk7_0 = X3
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk3_4(X1,X2,X3,X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_27,plain,
    ( X1 = X2
    | k4_tarski(k4_tarski(X3,X4),X1) != k4_tarski(k4_tarski(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_14]),c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_29,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_14]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( esk7_0 = X3
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)
    | k4_tarski(k4_tarski(X2,X3),X1) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( esk3_4(esk4_0,esk5_0,esk6_0,esk8_0) = esk7_0
    | k4_tarski(k4_tarski(X1,X2),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)) != esk8_0
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( esk3_4(esk4_0,esk5_0,esk6_0,esk8_0) = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( esk7_0 != k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_15])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(k4_tarski(X1,X2),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) != esk8_0
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_42,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( k4_tarski(k4_tarski(X1,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) != esk8_0
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_RG_S070I
% 0.21/0.38  # and selection function SelectVGNonCR.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.028 s
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.21/0.38  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.21/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.38  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.21/0.38  fof(t28_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_mcart_1(X1,X2,X3)=k3_mcart_1(X4,X5,X6)=>((X1=X4&X2=X5)&X3=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_mcart_1)).
% 0.21/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.21/0.38  fof(c_0_7, plain, ![X28, X29, X30, X31]:(X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|(~m1_subset_1(X31,k3_zfmisc_1(X28,X29,X30))|X31=k3_mcart_1(k5_mcart_1(X28,X29,X30,X31),k6_mcart_1(X28,X29,X30,X31),k7_mcart_1(X28,X29,X30,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.21/0.38  fof(c_0_8, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.38  fof(c_0_9, plain, ![X12, X13, X14]:k3_zfmisc_1(X12,X13,X14)=k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.38  fof(c_0_10, negated_conjecture, ![X37, X38, X39]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X37,esk4_0)|(~m1_subset_1(X38,esk5_0)|(~m1_subset_1(X39,esk6_0)|(esk8_0!=k3_mcart_1(X37,X38,X39)|esk7_0=X39))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.21/0.38  fof(c_0_11, plain, ![X15, X16, X17, X18]:((m1_subset_1(esk1_4(X15,X16,X17,X18),X15)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&((m1_subset_1(esk2_4(X15,X16,X17,X18),X16)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&((m1_subset_1(esk3_4(X15,X16,X17,X18),X17)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&(X18=k3_mcart_1(esk1_4(X15,X16,X17,X18),esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.21/0.38  fof(c_0_12, plain, ![X22, X23, X24, X25, X26, X27]:(((X22=X25|k3_mcart_1(X22,X23,X24)!=k3_mcart_1(X25,X26,X27))&(X23=X26|k3_mcart_1(X22,X23,X24)!=k3_mcart_1(X25,X26,X27)))&(X24=X27|k3_mcart_1(X22,X23,X24)!=k3_mcart_1(X25,X26,X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).
% 0.21/0.38  cnf(c_0_13, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  cnf(c_0_14, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_15, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_17, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_18, plain, (X1=X2|k3_mcart_1(X3,X4,X1)!=k3_mcart_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_19, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.21/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_22, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_24, plain, (X1=k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (esk7_0=X3|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_26, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk3_4(X1,X2,X3,X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.21/0.38  cnf(c_0_27, plain, (X1=X2|k4_tarski(k4_tarski(X3,X4),X1)!=k4_tarski(k4_tarski(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_14]), c_0_14])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.21/0.38  cnf(c_0_29, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_14]), c_0_15])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (esk7_0=X3|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_25, c_0_14])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (X1=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)|k4_tarski(k4_tarski(X2,X3),X1)!=esk8_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.21/0.38  cnf(c_0_34, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)=esk7_0|k4_tarski(k4_tarski(X1,X2),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0))!=esk8_0|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (esk7_0!=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_38, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_34, c_0_15])).
% 0.21/0.38  cnf(c_0_39, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, (k4_tarski(k4_tarski(X1,X2),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))!=esk8_0|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_37])).
% 0.21/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.21/0.38  cnf(c_0_42, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_39, c_0_15])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (k4_tarski(k4_tarski(X1,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))!=esk8_0|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(rw,[status(thm)],[c_0_33, c_0_36])).
% 0.21/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 47
% 0.21/0.38  # Proof object clause steps            : 34
% 0.21/0.38  # Proof object formula steps           : 13
% 0.21/0.38  # Proof object conjectures             : 23
% 0.21/0.38  # Proof object clause conjectures      : 20
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 14
% 0.21/0.38  # Proof object initial formulas used   : 6
% 0.21/0.38  # Proof object generating inferences   : 10
% 0.21/0.38  # Proof object simplifying inferences  : 32
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 6
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 16
% 0.21/0.38  # Removed in clause preprocessing      : 2
% 0.21/0.38  # Initial clauses in saturation        : 14
% 0.21/0.38  # Processed clauses                    : 42
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 8
% 0.21/0.38  # ...remaining for further processing  : 34
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 3
% 0.21/0.38  # Generated clauses                    : 66
% 0.21/0.38  # ...of the previous two non-trivial   : 65
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 63
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 3
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 31
% 0.21/0.38  #    Positive orientable unit clauses  : 7
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 4
% 0.21/0.38  #    Non-unit-clauses                  : 20
% 0.21/0.38  # Current number of unprocessed clauses: 35
% 0.21/0.38  # ...number of literals in the above   : 72
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 5
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 64
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 40
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.21/0.38  # Unit Clause-clause subsumption calls : 12
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 1
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2239
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.029 s
% 0.21/0.38  # System time              : 0.005 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
