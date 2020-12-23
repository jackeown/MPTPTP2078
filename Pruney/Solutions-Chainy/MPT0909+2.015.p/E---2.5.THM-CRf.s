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
% DateTime   : Thu Dec  3 11:00:10 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 358 expanded)
%              Number of clauses        :   34 ( 133 expanded)
%              Number of leaves         :    6 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 (2017 expanded)
%              Number of equality atoms :  115 (1264 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_mcart_1,conjecture,(
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

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

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
                       => X4 = X6 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_mcart_1])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,negated_conjecture,(
    ! [X33,X34,X35] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X33,esk4_0)
        | ~ m1_subset_1(X34,esk5_0)
        | ~ m1_subset_1(X35,esk6_0)
        | esk8_0 != k3_mcart_1(X33,X34,X35)
        | esk7_0 = X33 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_11,plain,
    ( X1 = k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( esk7_0 = X1
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

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
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk3_4(X1,X2,X3,X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_25,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_26,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( esk7_0 = X1
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

fof(c_0_32,plain,(
    ! [X26,X27] :
      ( k1_mcart_1(k4_tarski(X26,X27)) = X26
      & k2_mcart_1(k4_tarski(X26,X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_33,negated_conjecture,
    ( esk1_4(esk4_0,esk5_0,esk6_0,esk8_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

fof(c_0_34,plain,(
    ! [X22,X23,X24,X25] :
      ( ( k5_mcart_1(X22,X23,X24,X25) = k1_mcart_1(k1_mcart_1(X25))
        | ~ m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0 )
      & ( k6_mcart_1(X22,X23,X24,X25) = k2_mcart_1(k1_mcart_1(X25))
        | ~ m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0 )
      & ( k7_mcart_1(X22,X23,X24,X25) = k2_mcart_1(X25)
        | ~ m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_35,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(k4_tarski(esk7_0,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_37,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( esk3_4(esk4_0,esk5_0,esk6_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_13])).

cnf(c_0_40,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k4_tarski(k4_tarski(esk7_0,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) = k1_mcart_1(k1_mcart_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k4_tarski(esk7_0,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)) = k1_mcart_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk8_0)) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 09:35:56 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.12/0.35  # and selection function SelectNegativeLiterals.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.026 s
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.12/0.35  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.12/0.35  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.12/0.35  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.35  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.35  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.12/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.12/0.35  fof(c_0_7, plain, ![X15, X16, X17, X18]:((m1_subset_1(esk1_4(X15,X16,X17,X18),X15)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&((m1_subset_1(esk2_4(X15,X16,X17,X18),X16)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&((m1_subset_1(esk3_4(X15,X16,X17,X18),X17)|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))&(X18=k3_mcart_1(esk1_4(X15,X16,X17,X18),esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))|~m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))|(X15=k1_xboole_0|X16=k1_xboole_0|X17=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.12/0.35  fof(c_0_8, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.12/0.35  fof(c_0_9, plain, ![X12, X13, X14]:k3_zfmisc_1(X12,X13,X14)=k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.35  fof(c_0_10, negated_conjecture, ![X33, X34, X35]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X33,esk4_0)|(~m1_subset_1(X34,esk5_0)|(~m1_subset_1(X35,esk6_0)|(esk8_0!=k3_mcart_1(X33,X34,X35)|esk7_0=X33))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.12/0.35  cnf(c_0_11, plain, (X1=k3_mcart_1(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_12, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_15, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_16, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_17, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_18, negated_conjecture, (esk7_0=X1|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_19, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k4_tarski(k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1)),esk3_4(X2,X3,X4,X1))|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.12/0.35  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_14, c_0_13])).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_22, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_23, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_24, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk3_4(X1,X2,X3,X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_15, c_0_13])).
% 0.12/0.35  cnf(c_0_25, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk2_4(X1,X2,X3,X4),X2)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_16, c_0_13])).
% 0.12/0.35  cnf(c_0_26, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_17, c_0_13])).
% 0.12/0.35  cnf(c_0_27, negated_conjecture, (esk7_0=X1|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_18, c_0_12])).
% 0.12/0.35  cnf(c_0_28, negated_conjecture, (k4_tarski(k4_tarski(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.35  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_4(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.35  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_4(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.35  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk1_4(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.35  fof(c_0_32, plain, ![X26, X27]:(k1_mcart_1(k4_tarski(X26,X27))=X26&k2_mcart_1(k4_tarski(X26,X27))=X27), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.35  cnf(c_0_33, negated_conjecture, (esk1_4(esk4_0,esk5_0,esk6_0,esk8_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 0.12/0.35  fof(c_0_34, plain, ![X22, X23, X24, X25]:(((k5_mcart_1(X22,X23,X24,X25)=k1_mcart_1(k1_mcart_1(X25))|~m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))|(X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0))&(k6_mcart_1(X22,X23,X24,X25)=k2_mcart_1(k1_mcart_1(X25))|~m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))|(X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0)))&(k7_mcart_1(X22,X23,X24,X25)=k2_mcart_1(X25)|~m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))|(X22=k1_xboole_0|X23=k1_xboole_0|X24=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.12/0.35  cnf(c_0_35, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.35  cnf(c_0_36, negated_conjecture, (k4_tarski(k4_tarski(esk7_0,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),esk3_4(esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(rw,[status(thm)],[c_0_28, c_0_33])).
% 0.12/0.35  cnf(c_0_37, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.35  cnf(c_0_38, negated_conjecture, (esk3_4(esk4_0,esk5_0,esk6_0,esk8_0)=k2_mcart_1(esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.35  cnf(c_0_39, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_37, c_0_13])).
% 0.12/0.35  cnf(c_0_40, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.35  cnf(c_0_41, negated_conjecture, (k4_tarski(k4_tarski(esk7_0,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0))=esk8_0), inference(rw,[status(thm)],[c_0_36, c_0_38])).
% 0.12/0.35  cnf(c_0_42, negated_conjecture, (esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_43, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)=k1_mcart_1(k1_mcart_1(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.35  cnf(c_0_44, negated_conjecture, (k4_tarski(esk7_0,esk2_4(esk4_0,esk5_0,esk6_0,esk8_0))=k1_mcart_1(esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.35  cnf(c_0_45, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk8_0))!=esk7_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.35  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_44]), c_0_45]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 47
% 0.12/0.35  # Proof object clause steps            : 34
% 0.12/0.35  # Proof object formula steps           : 13
% 0.12/0.35  # Proof object conjectures             : 23
% 0.12/0.35  # Proof object clause conjectures      : 20
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 15
% 0.12/0.35  # Proof object initial formulas used   : 6
% 0.12/0.35  # Proof object generating inferences   : 9
% 0.12/0.35  # Proof object simplifying inferences  : 31
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 6
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 17
% 0.12/0.35  # Removed in clause preprocessing      : 2
% 0.12/0.35  # Initial clauses in saturation        : 15
% 0.12/0.35  # Processed clauses                    : 30
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 30
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 6
% 0.12/0.35  # Generated clauses                    : 18
% 0.12/0.35  # ...of the previous two non-trivial   : 22
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 18
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 24
% 0.12/0.35  #    Positive orientable unit clauses  : 12
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 4
% 0.12/0.35  #    Non-unit-clauses                  : 8
% 0.12/0.35  # Current number of unprocessed clauses: 4
% 0.12/0.35  # ...number of literals in the above   : 16
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 8
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 3
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 13
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 4
% 0.12/0.35  # BW rewrite match successes           : 4
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 1672
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.029 s
% 0.12/0.35  # System time              : 0.002 s
% 0.12/0.35  # Total time               : 0.031 s
% 0.12/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
