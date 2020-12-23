%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 239 expanded)
%              Number of clauses        :   54 ( 110 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 ( 796 expanded)
%              Number of equality atoms :   72 ( 141 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))
    & r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))
    & ( ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)
      | ~ r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)
      | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X23,X24,X25] : k3_zfmisc_1(X23,X24,X25) = k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(k1_mcart_1(X26),X27)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) )
      & ( r2_hidden(k2_mcart_1(X26),X28)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X29,X30,X31,X32] :
      ( ( k5_mcart_1(X29,X30,X31,X32) = k1_mcart_1(k1_mcart_1(X32))
        | ~ m1_subset_1(X32,k3_zfmisc_1(X29,X30,X31))
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0 )
      & ( k6_mcart_1(X29,X30,X31,X32) = k2_mcart_1(k1_mcart_1(X32))
        | ~ m1_subset_1(X32,k3_zfmisc_1(X29,X30,X31))
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0 )
      & ( k7_mcart_1(X29,X30,X31,X32) = k2_mcart_1(X32)
        | ~ m1_subset_1(X32,k3_zfmisc_1(X29,X30,X31))
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_23,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_28,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X17)
      | ~ r1_tarski(X17,X16)
      | ~ r1_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_32,plain,(
    ! [X15] : r1_xboole_0(X15,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk8_0)) = k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk8_0)) = k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_37,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)
    | ~ r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0) = k2_mcart_1(esk8_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_39])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk6_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(esk5_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_56])).

fof(c_0_70,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.19/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.38  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.19/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.19/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))&(r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))&(~r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)|~r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X23, X24, X25]:k3_zfmisc_1(X23,X24,X25)=k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.38  fof(c_0_13, plain, ![X26, X27, X28]:((r2_hidden(k1_mcart_1(X26),X27)|~r2_hidden(X26,k2_zfmisc_1(X27,X28)))&(r2_hidden(k2_mcart_1(X26),X28)|~r2_hidden(X26,k2_zfmisc_1(X27,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_16, plain, ![X29, X30, X31, X32]:(((k5_mcart_1(X29,X30,X31,X32)=k1_mcart_1(k1_mcart_1(X32))|~m1_subset_1(X32,k3_zfmisc_1(X29,X30,X31))|(X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0))&(k6_mcart_1(X29,X30,X31,X32)=k2_mcart_1(k1_mcart_1(X32))|~m1_subset_1(X32,k3_zfmisc_1(X29,X30,X31))|(X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0)))&(k7_mcart_1(X29,X30,X31,X32)=k2_mcart_1(X32)|~m1_subset_1(X32,k3_zfmisc_1(X29,X30,X31))|(X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.19/0.38  cnf(c_0_17, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_19, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_21, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_22, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|~v1_xboole_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.38  fof(c_0_23, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_24, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  cnf(c_0_26, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_19, c_0_15])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_20, c_0_15])).
% 0.19/0.38  cnf(c_0_28, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_21, c_0_15])).
% 0.19/0.38  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  fof(c_0_31, plain, ![X16, X17]:(v1_xboole_0(X17)|(~r1_tarski(X17,X16)|~r1_xboole_0(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.19/0.38  fof(c_0_32, plain, ![X15]:r1_xboole_0(X15,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk8_0))=k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk8_0))=k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.19/0.38  cnf(c_0_37, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(k2_mcart_1(esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.19/0.38  cnf(c_0_40, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  fof(c_0_42, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (~r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)|~r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_46, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_37, c_0_15])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  cnf(c_0_48, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)=k2_mcart_1(esk8_0)|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_27])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (~r1_tarski(esk7_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.38  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_33])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_35])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_39])])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (~r1_tarski(esk6_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_48])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (~r1_tarski(esk5_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_48])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (r1_tarski(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_59])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_60])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (~r1_tarski(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_56])).
% 0.19/0.38  fof(c_0_70, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.19/0.38  cnf(c_0_73, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_73])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 75
% 0.19/0.38  # Proof object clause steps            : 54
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 37
% 0.19/0.38  # Proof object clause conjectures      : 34
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 20
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 28
% 0.19/0.38  # Proof object simplifying inferences  : 13
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 20
% 0.19/0.38  # Processed clauses                    : 124
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 26
% 0.19/0.38  # ...remaining for further processing  : 98
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 9
% 0.19/0.38  # Backward-rewritten                   : 16
% 0.19/0.38  # Generated clauses                    : 158
% 0.19/0.38  # ...of the previous two non-trivial   : 152
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 158
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 73
% 0.19/0.38  #    Positive orientable unit clauses  : 15
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 9
% 0.19/0.38  #    Non-unit-clauses                  : 49
% 0.19/0.38  # Current number of unprocessed clauses: 45
% 0.19/0.38  # ...number of literals in the above   : 121
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 26
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 462
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 329
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 30
% 0.19/0.38  # Unit Clause-clause subsumption calls : 108
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 10
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3294
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
