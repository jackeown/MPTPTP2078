%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 252 expanded)
%              Number of clauses        :   59 ( 116 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  226 ( 836 expanded)
%              Number of equality atoms :   81 ( 162 expanded)
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

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))
    & m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
    & ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
      | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
      | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X31,X32,X33] : k3_zfmisc_1(X31,X32,X33) = k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(k1_mcart_1(X34),X35)
        | ~ r2_hidden(X34,k2_zfmisc_1(X35,X36)) )
      & ( r2_hidden(k2_mcart_1(X34),X36)
        | ~ r2_hidden(X34,k2_zfmisc_1(X35,X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X37,X38,X39,X40] :
      ( ( k5_mcart_1(X37,X38,X39,X40) = k1_mcart_1(k1_mcart_1(X40))
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k6_mcart_1(X37,X38,X39,X40) = k2_mcart_1(k1_mcart_1(X40))
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k7_mcart_1(X37,X38,X39,X40) = k2_mcart_1(X40)
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X21,X20)
        | r1_tarski(X21,X19)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r1_tarski(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r2_hidden(esk3_2(X23,X24),X24)
        | ~ r1_tarski(esk3_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) )
      & ( r2_hidden(esk3_2(X23,X24),X24)
        | r1_tarski(esk3_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_24,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_25,plain,(
    ! [X26] : ~ v1_xboole_0(k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_29,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk10_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_40,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk9_0,k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

fof(c_0_43,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk10_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_48,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_38]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_39]),c_0_33])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_17])).

fof(c_0_58,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_59,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0) = k2_mcart_1(esk10_0)
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_28])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_1(esk9_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_54])])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_63]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_1(esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_63]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_75])).

cnf(c_0_81,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t76_mcart_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 0.20/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.38  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.20/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(X3))=>![X7]:(m1_subset_1(X7,k3_zfmisc_1(X1,X2,X3))=>(r2_hidden(X7,k3_zfmisc_1(X4,X5,X6))=>((r2_hidden(k5_mcart_1(X1,X2,X3,X7),X4)&r2_hidden(k6_mcart_1(X1,X2,X3,X7),X5))&r2_hidden(k7_mcart_1(X1,X2,X3,X7),X6)))))))), inference(assume_negation,[status(cth)],[t76_mcart_1])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))&(m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&(~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X31, X32, X33]:k3_zfmisc_1(X31,X32,X33)=k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.38  fof(c_0_15, plain, ![X34, X35, X36]:((r2_hidden(k1_mcart_1(X34),X35)|~r2_hidden(X34,k2_zfmisc_1(X35,X36)))&(r2_hidden(k2_mcart_1(X34),X36)|~r2_hidden(X34,k2_zfmisc_1(X35,X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_18, plain, ![X37, X38, X39, X40]:(((k5_mcart_1(X37,X38,X39,X40)=k1_mcart_1(k1_mcart_1(X40))|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))&(k6_mcart_1(X37,X38,X39,X40)=k2_mcart_1(k1_mcart_1(X40))|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0)))&(k7_mcart_1(X37,X38,X39,X40)=k2_mcart_1(X40)|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.20/0.38  cnf(c_0_19, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_21, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk10_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_23, plain, ![X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X21,X20)|r1_tarski(X21,X19)|X20!=k1_zfmisc_1(X19))&(~r1_tarski(X22,X19)|r2_hidden(X22,X20)|X20!=k1_zfmisc_1(X19)))&((~r2_hidden(esk3_2(X23,X24),X24)|~r1_tarski(esk3_2(X23,X24),X23)|X24=k1_zfmisc_1(X23))&(r2_hidden(esk3_2(X23,X24),X24)|r1_tarski(esk3_2(X23,X24),X23)|X24=k1_zfmisc_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.38  fof(c_0_24, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.38  fof(c_0_25, plain, ![X26]:~v1_xboole_0(k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_27, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 0.20/0.38  cnf(c_0_29, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_31, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_33, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk7_0)), inference(spm,[status(thm)],[c_0_19, c_0_26])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk10_0))=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_36, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_37, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_29, c_0_17])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_40, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk9_0,k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.38  fof(c_0_43, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk10_0)),esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk10_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_28])).
% 0.20/0.38  cnf(c_0_48, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_38]), c_0_33])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_39]), c_0_33])).
% 0.20/0.38  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  cnf(c_0_53, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(k2_mcart_1(esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_36, c_0_20])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_57, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_48, c_0_17])).
% 0.20/0.38  fof(c_0_58, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  fof(c_0_59, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.38  cnf(c_0_63, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|~r2_hidden(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0),esk9_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk10_0)=k2_mcart_1(esk10_0)|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_28])).
% 0.20/0.38  cnf(c_0_67, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.38  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_60])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_53, c_0_34])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_61])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_1(esk9_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_54])])).
% 0.20/0.38  cnf(c_0_75, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_63]), c_0_70])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_1(esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_63]), c_0_72])).
% 0.20/0.38  cnf(c_0_78, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_76])).
% 0.20/0.38  cnf(c_0_80, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_75])).
% 0.20/0.38  cnf(c_0_81, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.38  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_81])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 83
% 0.20/0.38  # Proof object clause steps            : 59
% 0.20/0.38  # Proof object formula steps           : 24
% 0.20/0.38  # Proof object conjectures             : 42
% 0.20/0.38  # Proof object clause conjectures      : 39
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 21
% 0.20/0.38  # Proof object initial formulas used   : 12
% 0.20/0.38  # Proof object generating inferences   : 32
% 0.20/0.38  # Proof object simplifying inferences  : 18
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 12
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 26
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 25
% 0.20/0.38  # Processed clauses                    : 137
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 25
% 0.20/0.38  # ...remaining for further processing  : 112
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 9
% 0.20/0.38  # Backward-rewritten                   : 16
% 0.20/0.38  # Generated clauses                    : 159
% 0.20/0.38  # ...of the previous two non-trivial   : 147
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 157
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
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
% 0.20/0.38  # Current number of processed clauses  : 62
% 0.20/0.38  #    Positive orientable unit clauses  : 23
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 13
% 0.20/0.38  #    Non-unit-clauses                  : 26
% 0.20/0.38  # Current number of unprocessed clauses: 57
% 0.20/0.38  # ...number of literals in the above   : 151
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 51
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 229
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 152
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 16
% 0.20/0.38  # Unit Clause-clause subsumption calls : 78
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 10
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3448
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
