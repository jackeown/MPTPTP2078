%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 255 expanded)
%              Number of clauses        :   56 ( 118 expanded)
%              Number of leaves         :    8 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  196 ( 819 expanded)
%              Number of equality atoms :   78 ( 147 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X1))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X2))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X3))
             => ! [X7] :
                  ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
                 => ( r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
                   => ( r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)
                      & r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5)
                      & r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

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

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X1))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X2))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X3))
               => ! [X7] :
                    ( m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))
                   => ( r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))
                     => ( r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)
                        & r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5)
                        & r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_mcart_1])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))
    & r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))
    & ( ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)
      | ~ r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)
      | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X17,X18,X19] : k3_zfmisc_1(X17,X18,X19) = k2_zfmisc_1(k2_zfmisc_1(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X23,X24,X25,X26] :
      ( ( k5_mcart_1(X23,X24,X25,X26) = k1_mcart_1(k1_mcart_1(X26))
        | ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( k6_mcart_1(X23,X24,X25,X26) = k2_mcart_1(k1_mcart_1(X26))
        | ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( k7_mcart_1(X23,X24,X25,X26) = k2_mcart_1(X26)
        | ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_12,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(k1_mcart_1(X20),X21)
        | ~ r2_hidden(X20,k2_zfmisc_1(X21,X22)) )
      & ( r2_hidden(k2_mcart_1(X20),X22)
        | ~ r2_hidden(X20,k2_zfmisc_1(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)
    | ~ r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0) = k1_mcart_1(k1_mcart_1(esk8_0))
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk8_0)) = k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_31,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_32,plain,(
    ! [X13,X14] :
      ( v1_xboole_0(X14)
      | ~ r1_tarski(X14,X13)
      | ~ r1_xboole_0(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_14])).

fof(c_0_38,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0) = k2_mcart_1(esk8_0)
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

fof(c_0_44,plain,(
    ! [X12] : r1_xboole_0(X12,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ r1_xboole_0(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ r1_xboole_0(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_1(k2_zfmisc_1(esk5_0,esk6_0)),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_49])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_1(k2_zfmisc_1(esk5_0,esk6_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ r1_xboole_0(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_49])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_1(k2_zfmisc_1(esk5_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_70,c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:27:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074I
% 0.12/0.37  # and selection function SelectCQIArEqFirst.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.12/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.37  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.12/0.37  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.12/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.37  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))&(r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))&(~r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)|~r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.37  fof(c_0_10, plain, ![X17, X18, X19]:k3_zfmisc_1(X17,X18,X19)=k2_zfmisc_1(k2_zfmisc_1(X17,X18),X19), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.37  fof(c_0_11, plain, ![X23, X24, X25, X26]:(((k5_mcart_1(X23,X24,X25,X26)=k1_mcart_1(k1_mcart_1(X26))|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0))&(k6_mcart_1(X23,X24,X25,X26)=k2_mcart_1(k1_mcart_1(X26))|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0)))&(k7_mcart_1(X23,X24,X25,X26)=k2_mcart_1(X26)|~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))|(X23=k1_xboole_0|X24=k1_xboole_0|X25=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X20, X21, X22]:((r2_hidden(k1_mcart_1(X20),X21)|~r2_hidden(X20,k2_zfmisc_1(X21,X22)))&(r2_hidden(k2_mcart_1(X20),X22)|~r2_hidden(X20,k2_zfmisc_1(X21,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_15, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_17, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_19, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_20, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_16, c_0_14])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.37  cnf(c_0_23, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_24, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.12/0.37  fof(c_0_25, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (~r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)|~r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)=k1_mcart_1(k1_mcart_1(esk8_0))|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk8_0))=k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.12/0.37  cnf(c_0_31, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_32, plain, ![X13, X14]:(v1_xboole_0(X14)|(~r1_tarski(X14,X13)|~r1_xboole_0(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.37  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|~r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_37, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_31, c_0_14])).
% 0.12/0.37  fof(c_0_38, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.37  cnf(c_0_39, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (r1_tarski(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)=k2_mcart_1(esk8_0)|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_21])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(k2_mcart_1(esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.12/0.37  fof(c_0_44, plain, ![X12]:r1_xboole_0(X12,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.12/0.37  cnf(c_0_45, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_46, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (v1_xboole_0(esk7_0)|~r1_xboole_0(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.12/0.37  cnf(c_0_49, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.37  cnf(c_0_50, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_18])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (r1_tarski(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_51])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_52])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_43])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_mcart_1(esk1_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_17, c_0_53])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk6_0)|~r1_xboole_0(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_54])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_1(k2_zfmisc_1(esk5_0,esk6_0)),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_57])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (esk2_0=k1_xboole_0|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_49])])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (r2_hidden(k2_mcart_1(esk1_1(k2_zfmisc_1(esk5_0,esk6_0))),esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_60])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (r1_tarski(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_61])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (esk2_0=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_62])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_63])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (v1_xboole_0(esk5_0)|~r1_xboole_0(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_64])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_49])])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, (r2_hidden(k1_mcart_1(esk1_1(k2_zfmisc_1(esk5_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_60])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_69])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_70, c_0_71]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 73
% 0.12/0.37  # Proof object clause steps            : 56
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 44
% 0.12/0.37  # Proof object clause conjectures      : 41
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 17
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 32
% 0.12/0.37  # Proof object simplifying inferences  : 17
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 17
% 0.12/0.37  # Processed clauses                    : 71
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 71
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 9
% 0.12/0.37  # Backward-rewritten                   : 8
% 0.12/0.37  # Generated clauses                    : 68
% 0.12/0.37  # ...of the previous two non-trivial   : 54
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 64
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
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
% 0.12/0.37  # Current number of processed clauses  : 33
% 0.12/0.37  #    Positive orientable unit clauses  : 19
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 13
% 0.12/0.37  # Current number of unprocessed clauses: 12
% 0.12/0.37  # ...number of literals in the above   : 30
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 39
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 61
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 30
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.12/0.37  # Unit Clause-clause subsumption calls : 10
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1995
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.026 s
% 0.12/0.37  # System time              : 0.008 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
