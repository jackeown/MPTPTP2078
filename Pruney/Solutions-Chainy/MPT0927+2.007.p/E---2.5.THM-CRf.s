%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:34 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 321 expanded)
%              Number of clauses        :   51 ( 150 expanded)
%              Number of leaves         :    7 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :  230 (1130 expanded)
%              Number of equality atoms :  127 ( 316 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(X1))
     => ! [X6] :
          ( m1_subset_1(X6,k1_zfmisc_1(X2))
         => ! [X7] :
              ( m1_subset_1(X7,k1_zfmisc_1(X3))
             => ! [X8] :
                  ( m1_subset_1(X8,k1_zfmisc_1(X4))
                 => ! [X9] :
                      ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
                     => ( r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))
                       => ( r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)
                          & r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6)
                          & r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7)
                          & r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k1_zfmisc_1(X1))
       => ! [X6] :
            ( m1_subset_1(X6,k1_zfmisc_1(X2))
           => ! [X7] :
                ( m1_subset_1(X7,k1_zfmisc_1(X3))
               => ! [X8] :
                    ( m1_subset_1(X8,k1_zfmisc_1(X4))
                   => ! [X9] :
                        ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
                       => ( r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))
                         => ( r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)
                            & r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6)
                            & r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7)
                            & r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t87_mcart_1])).

fof(c_0_8,plain,(
    ! [X16,X17,X18,X19] : k4_zfmisc_1(X16,X17,X18,X19) = k2_zfmisc_1(k3_zfmisc_1(X16,X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X13,X14,X15] : k3_zfmisc_1(X13,X14,X15) = k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & r2_hidden(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & ( ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
      | ~ r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)
      | ~ r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
      | ~ r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(k1_mcart_1(X20),X21)
        | ~ r2_hidden(X20,k2_zfmisc_1(X21,X22)) )
      & ( r2_hidden(k2_mcart_1(X20),X22)
        | ~ r2_hidden(X20,k2_zfmisc_1(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( k8_mcart_1(X23,X24,X25,X26,X27) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X27)))
        | ~ m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 )
      & ( k9_mcart_1(X23,X24,X25,X26,X27) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X27)))
        | ~ m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 )
      & ( k10_mcart_1(X23,X24,X25,X26,X27) = k2_mcart_1(k1_mcart_1(X27))
        | ~ m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 )
      & ( k11_mcart_1(X23,X24,X25,X26,X27) = k2_mcart_1(X27)
        | ~ m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk9_0)),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_19])).

cnf(c_0_24,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) = k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
    | ~ r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)
    | ~ r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
    | ~ r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_32,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)
    | ~ r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
    | ~ r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

cnf(c_0_36,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_37,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_38,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | ~ r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)
    | ~ r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) = k2_mcart_1(k1_mcart_1(esk9_0))
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk9_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_42,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5)
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_46,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0) = k2_mcart_1(esk9_0)
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_50])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_60,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_50])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_50])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_35,c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t87_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X2))=>![X7]:(m1_subset_1(X7,k1_zfmisc_1(X3))=>![X8]:(m1_subset_1(X8,k1_zfmisc_1(X4))=>![X9]:(m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))=>(r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))=>(((r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)&r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6))&r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7))&r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_mcart_1)).
% 0.20/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.20/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.38  fof(t61_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>(((k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))&k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5))))&k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5)))&k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 0.20/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X2))=>![X7]:(m1_subset_1(X7,k1_zfmisc_1(X3))=>![X8]:(m1_subset_1(X8,k1_zfmisc_1(X4))=>![X9]:(m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))=>(r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))=>(((r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)&r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6))&r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7))&r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8))))))))), inference(assume_negation,[status(cth)],[t87_mcart_1])).
% 0.20/0.38  fof(c_0_8, plain, ![X16, X17, X18, X19]:k4_zfmisc_1(X16,X17,X18,X19)=k2_zfmisc_1(k3_zfmisc_1(X16,X17,X18),X19), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.20/0.38  fof(c_0_9, plain, ![X13, X14, X15]:k3_zfmisc_1(X13,X14,X15)=k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.38  fof(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&(r2_hidden(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))&(~r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)|~r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)|~r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)|~r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.38  cnf(c_0_11, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_13, plain, ![X20, X21, X22]:((r2_hidden(k1_mcart_1(X20),X21)|~r2_hidden(X20,k2_zfmisc_1(X21,X22)))&(r2_hidden(k2_mcart_1(X20),X22)|~r2_hidden(X20,k2_zfmisc_1(X21,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.38  cnf(c_0_16, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  fof(c_0_18, plain, ![X23, X24, X25, X26, X27]:((((k8_mcart_1(X23,X24,X25,X26,X27)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X27)))|~m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0))&(k9_mcart_1(X23,X24,X25,X26,X27)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X27)))|~m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0)))&(k10_mcart_1(X23,X24,X25,X26,X27)=k2_mcart_1(k1_mcart_1(X27))|~m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0)))&(k11_mcart_1(X23,X24,X25,X26,X27)=k2_mcart_1(X27)|~m1_subset_1(X27,k4_zfmisc_1(X23,X24,X25,X26))|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_mcart_1])])])])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_20, plain, (k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk9_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_22, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk9_0)),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_16, c_0_19])).
% 0.20/0.38  cnf(c_0_24, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k9_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_20, c_0_15])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_21, c_0_15])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))),esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))=k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  cnf(c_0_28, plain, (k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (~r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)|~r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)|~r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)|~r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|r2_hidden(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_31, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k8_mcart_1(X1,X2,X3,X4,X5)=k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_28, c_0_15])).
% 0.20/0.38  cnf(c_0_32, plain, (k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk5_0)|~r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)|~r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_25])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))),esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_23])).
% 0.20/0.38  cnf(c_0_36, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k10_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(k1_mcart_1(X5))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_32, c_0_15])).
% 0.20/0.38  cnf(c_0_37, plain, (k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_38, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|~r2_hidden(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk7_0)|~r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)=k2_mcart_1(k1_mcart_1(esk9_0))|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk9_0)),esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.20/0.38  cnf(c_0_42, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k11_mcart_1(X1,X2,X3,X4,X5)=k2_mcart_1(X5)|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[c_0_37, c_0_15])).
% 0.20/0.38  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk9_0)=k2_mcart_1(esk9_0)|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(k2_mcart_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,esk8_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.20/0.38  cnf(c_0_50, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (~r2_hidden(X1,esk7_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_51])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_50])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (~r2_hidden(X1,esk6_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_41])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (esk1_0=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_50])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_59])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_26])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_50])])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_35, c_0_63]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 65
% 0.20/0.38  # Proof object clause steps            : 51
% 0.20/0.38  # Proof object formula steps           : 14
% 0.20/0.38  # Proof object conjectures             : 39
% 0.20/0.38  # Proof object clause conjectures      : 36
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 25
% 0.20/0.38  # Proof object simplifying inferences  : 23
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 17
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 15
% 0.20/0.38  # Processed clauses                    : 57
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 57
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 13
% 0.20/0.38  # Backward-rewritten                   : 6
% 0.20/0.38  # Generated clauses                    : 36
% 0.20/0.38  # ...of the previous two non-trivial   : 39
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 35
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 22
% 0.20/0.38  #    Positive orientable unit clauses  : 11
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 10
% 0.20/0.38  # Current number of unprocessed clauses: 12
% 0.20/0.38  # ...number of literals in the above   : 42
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 37
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 106
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 15
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.38  # Unit Clause-clause subsumption calls : 8
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2023
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.034 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
