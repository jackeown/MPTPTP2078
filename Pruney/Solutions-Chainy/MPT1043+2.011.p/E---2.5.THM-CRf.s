%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 (2639 expanded)
%              Number of clauses        :   41 (1084 expanded)
%              Number of leaves         :    9 ( 661 expanded)
%              Depth                    :   15
%              Number of atoms          :  169 (8924 expanded)
%              Number of equality atoms :   12 ( 257 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(fc2_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2)
        & v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => v1_xboole_0(k5_partfun1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_2])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,plain,(
    ! [X23,X24,X25,X26] :
      ( ( v1_funct_1(X26)
        | ~ r2_hidden(X26,k5_partfun1(X23,X24,X25))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v1_funct_2(X26,X23,X24)
        | ~ r2_hidden(X26,k5_partfun1(X23,X24,X25))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ r2_hidden(X26,k5_partfun1(X23,X24,X25))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & ~ r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] :
      ( ( X21 = k1_xboole_0
        | r2_hidden(X22,k1_funct_2(X20,X21))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X20 != k1_xboole_0
        | r2_hidden(X22,k1_funct_2(X20,X21))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(X1,esk2_0,esk3_0)
    | ~ r2_hidden(X1,k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_23])])).

fof(c_0_31,plain,(
    ! [X17,X18,X19] :
      ( v1_xboole_0(X17)
      | ~ v1_xboole_0(X18)
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_xboole_0(k5_partfun1(X17,X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_12])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1))
    | r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),esk2_0,esk3_0)
    | r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_12])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),k1_funct_2(esk2_0,esk3_0))
    | r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_22]),c_0_23])]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_40]),c_0_32])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_44,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_xboole_0)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_46,plain,
    ( r2_hidden(X2,k1_funct_2(X1,X3))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k1_funct_2(k1_xboole_0,X2))
    | ~ v1_funct_2(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_xboole_0,X2)
    | ~ v1_funct_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)))
    | ~ m1_subset_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1),k1_xboole_0,k1_xboole_0)
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_42]),c_0_42]),c_0_42]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_42]),c_0_42]),c_0_50]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_42]),c_0_42]),c_0_42]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1))
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_42]),c_0_42]),c_0_50]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DN
% 0.13/0.39  # and selection function PSelectComplexExceptRRHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 0.13/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.39  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.13/0.39  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.13/0.39  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 0.13/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.39  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.13/0.39  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_11, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 0.13/0.39  fof(c_0_14, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|~v1_xboole_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.39  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_16, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.39  fof(c_0_17, plain, ![X23, X24, X25, X26]:(((v1_funct_1(X26)|~r2_hidden(X26,k5_partfun1(X23,X24,X25))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(v1_funct_2(X26,X23,X24)|~r2_hidden(X26,k5_partfun1(X23,X24,X25))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))&(m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~r2_hidden(X26,k5_partfun1(X23,X24,X25))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.13/0.39  fof(c_0_18, negated_conjecture, ((v1_funct_1(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&~r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.39  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_24, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_25, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_26, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  fof(c_0_27, plain, ![X20, X21, X22]:((X21=k1_xboole_0|r2_hidden(X22,k1_funct_2(X20,X21))|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(X20!=k1_xboole_0|r2_hidden(X22,k1_funct_2(X20,X21))|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~r2_hidden(X1,k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_23])])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_2(X1,esk2_0,esk3_0)|~r2_hidden(X1,k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_23])])).
% 0.13/0.39  fof(c_0_31, plain, ![X17, X18, X19]:(v1_xboole_0(X17)|~v1_xboole_0(X18)|~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_xboole_0(k5_partfun1(X17,X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (~r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_26, c_0_12])).
% 0.13/0.39  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_12])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1))|r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_12])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),esk2_0,esk3_0)|r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_12])).
% 0.13/0.39  cnf(c_0_38, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_2(k5_partfun1(esk2_0,esk3_0,esk4_0),X1),k1_funct_2(esk2_0,esk3_0))|r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_22]), c_0_23])]), c_0_39])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_40]), c_0_32])).
% 0.13/0.39  cnf(c_0_43, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.39  fof(c_0_44, plain, ![X11]:(~r1_tarski(X11,k1_xboole_0)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.13/0.39  cnf(c_0_46, plain, (r2_hidden(X2,k1_funct_2(X1,X3))|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_47, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_45])).
% 0.13/0.39  cnf(c_0_49, plain, (r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))|~v1_funct_2(X1,k1_xboole_0,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.39  cnf(c_0_51, plain, (r1_tarski(X1,k1_funct_2(k1_xboole_0,X2))|~v1_funct_2(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_xboole_0,X2)|~v1_funct_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)))|~m1_subset_1(esk1_2(X1,k1_funct_2(k1_xboole_0,X2)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_11, c_0_49])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1),k1_xboole_0,k1_xboole_0)|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_42]), c_0_42]), c_0_42]), c_0_50]), c_0_50]), c_0_50])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_42]), c_0_42]), c_0_50]), c_0_50])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (~v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_42]), c_0_42]), c_0_42]), c_0_50]), c_0_50]), c_0_50])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (~v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),k1_funct_2(k1_xboole_0,k1_xboole_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_53])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk1_2(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1))|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_42]), c_0_42]), c_0_50]), c_0_50])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 59
% 0.13/0.39  # Proof object clause steps            : 41
% 0.13/0.39  # Proof object formula steps           : 18
% 0.13/0.39  # Proof object conjectures             : 26
% 0.13/0.39  # Proof object clause conjectures      : 23
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 15
% 0.13/0.39  # Proof object initial formulas used   : 9
% 0.13/0.39  # Proof object generating inferences   : 20
% 0.13/0.39  # Proof object simplifying inferences  : 39
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 9
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 17
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 17
% 0.13/0.39  # Processed clauses                    : 212
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 55
% 0.13/0.39  # ...remaining for further processing  : 156
% 0.13/0.39  # Other redundant clauses eliminated   : 1
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 1
% 0.13/0.39  # Backward-rewritten                   : 40
% 0.13/0.39  # Generated clauses                    : 197
% 0.13/0.39  # ...of the previous two non-trivial   : 222
% 0.13/0.39  # Contextual simplify-reflections      : 6
% 0.13/0.39  # Paramodulations                      : 196
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 1
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 97
% 0.13/0.39  #    Positive orientable unit clauses  : 10
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 4
% 0.13/0.39  #    Non-unit-clauses                  : 83
% 0.13/0.39  # Current number of unprocessed clauses: 40
% 0.13/0.39  # ...number of literals in the above   : 159
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 58
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1907
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 971
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 58
% 0.13/0.39  # Unit Clause-clause subsumption calls : 110
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 12
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 6428
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.044 s
% 0.13/0.39  # System time              : 0.001 s
% 0.13/0.39  # Total time               : 0.045 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
