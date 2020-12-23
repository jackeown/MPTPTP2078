%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 283 expanded)
%              Number of clauses        :   58 ( 132 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  217 ( 916 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

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

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    ! [X24,X25,X26] : k3_zfmisc_1(X24,X25,X26) = k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(k1_mcart_1(X27),X28)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) )
      & ( r2_hidden(k2_mcart_1(X27),X29)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X30,X31,X32,X33] :
      ( ( k5_mcart_1(X30,X31,X32,X33) = k1_mcart_1(k1_mcart_1(X33))
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( k6_mcart_1(X30,X31,X32,X33) = k2_mcart_1(k1_mcart_1(X33))
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( k7_mcart_1(X30,X31,X32,X33) = k2_mcart_1(X33)
        | ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 ) ) ),
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
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_15])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_26,plain,(
    ! [X16] : r1_xboole_0(X16,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk8_0)) = k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X18)
      | ~ r1_tarski(X18,X17)
      | ~ r1_xboole_0(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)
    | ~ r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_39,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0) = k1_mcart_1(k1_mcart_1(esk8_0))
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_49,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_15])).

cnf(c_0_50,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_57,negated_conjecture,
    ( k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0) = k2_mcart_1(esk8_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_51])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_27])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(esk5_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_59])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.043 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.19/0.40  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.40  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.40  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.19/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.19/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.19/0.40  fof(c_0_11, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))&(r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))&(~r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)|~r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.40  fof(c_0_12, plain, ![X24, X25, X26]:k3_zfmisc_1(X24,X25,X26)=k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.40  fof(c_0_13, plain, ![X27, X28, X29]:((r2_hidden(k1_mcart_1(X27),X28)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))&(r2_hidden(k2_mcart_1(X27),X29)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.40  cnf(c_0_14, negated_conjecture, (r2_hidden(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_15, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  fof(c_0_16, plain, ![X30, X31, X32, X33]:(((k5_mcart_1(X30,X31,X32,X33)=k1_mcart_1(k1_mcart_1(X33))|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))&(k6_mcart_1(X30,X31,X32,X33)=k2_mcart_1(k1_mcart_1(X33))|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0)))&(k7_mcart_1(X30,X31,X32,X33)=k2_mcart_1(X33)|~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|(X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.19/0.40  cnf(c_0_17, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.40  cnf(c_0_19, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_21, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_23, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_19, c_0_15])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_20, c_0_15])).
% 0.19/0.40  fof(c_0_25, plain, ![X14, X15]:(~r1_xboole_0(X14,X15)|r1_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.40  fof(c_0_26, plain, ![X16]:r1_xboole_0(X16,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk8_0)),esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk8_0))=k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_29, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_30, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.40  fof(c_0_31, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  fof(c_0_32, plain, ![X17, X18]:(v1_xboole_0(X18)|(~r1_tarski(X18,X17)|~r1_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.19/0.40  cnf(c_0_33, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_34, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  fof(c_0_35, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (~r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)|~r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.40  cnf(c_0_38, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_29, c_0_15])).
% 0.19/0.40  cnf(c_0_39, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_42, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_43, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.40  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|~r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk5_0)|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (k5_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)=k1_mcart_1(k1_mcart_1(esk8_0))|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.19/0.40  cnf(c_0_49, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_39, c_0_15])).
% 0.19/0.40  cnf(c_0_50, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (r2_hidden(k2_mcart_1(esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.40  cnf(c_0_52, plain, (v1_xboole_0(k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.40  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.40  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (k7_mcart_1(esk2_0,esk3_0,esk4_0,esk8_0)=k2_mcart_1(esk8_0)|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_24])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.40  cnf(c_0_59, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.19/0.40  cnf(c_0_61, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (r1_tarski(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_51])])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_27])).
% 0.19/0.40  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (~r1_tarski(esk5_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (r1_tarski(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_62])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (r1_tarski(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_63])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (~r1_tarski(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_59])).
% 0.19/0.40  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_53])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.19/0.40  cnf(c_0_77, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_59])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_77])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 79
% 0.19/0.40  # Proof object clause steps            : 58
% 0.19/0.40  # Proof object formula steps           : 21
% 0.19/0.40  # Proof object conjectures             : 35
% 0.19/0.40  # Proof object clause conjectures      : 32
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 20
% 0.19/0.40  # Proof object initial formulas used   : 10
% 0.19/0.40  # Proof object generating inferences   : 32
% 0.19/0.40  # Proof object simplifying inferences  : 14
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 10
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 21
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 20
% 0.19/0.40  # Processed clauses                    : 151
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 43
% 0.19/0.40  # ...remaining for further processing  : 108
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 8
% 0.19/0.40  # Backward-rewritten                   : 17
% 0.19/0.40  # Generated clauses                    : 210
% 0.19/0.40  # ...of the previous two non-trivial   : 204
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 210
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 83
% 0.19/0.40  #    Positive orientable unit clauses  : 17
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 9
% 0.19/0.40  #    Non-unit-clauses                  : 57
% 0.19/0.40  # Current number of unprocessed clauses: 69
% 0.19/0.40  # ...number of literals in the above   : 168
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 26
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 581
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 424
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 31
% 0.19/0.40  # Unit Clause-clause subsumption calls : 127
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 19
% 0.19/0.40  # BW rewrite match successes           : 2
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 3947
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.053 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.059 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
