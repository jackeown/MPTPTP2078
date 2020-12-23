%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 515 expanded)
%              Number of clauses        :   43 ( 206 expanded)
%              Number of leaves         :   10 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          :  233 (1835 expanded)
%              Number of equality atoms :   42 ( 417 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t170_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,k9_setfam_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) )
     => ? [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => k11_relat_1(X3,X4) = k1_funct_1(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_funct_2)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(s3_relset_1__e2_192__funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,k9_setfam_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) )
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => ( r2_hidden(X3,k2_subset_1(X1))
             => r1_tarski(k1_funct_1(X2,X3),k2_subset_1(X1)) ) )
       => ? [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
            & ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,k2_subset_1(X1))
                 => k11_relat_1(X3,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_relset_1__e2_192__funct_2)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_10,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,k9_setfam_1(X1))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) )
       => ? [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
            & ! [X4] :
                ( r2_hidden(X4,X1)
               => k11_relat_1(X3,X4) = k1_funct_1(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t170_funct_2])).

fof(c_0_12,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ v1_funct_1(X21)
      | ~ v1_funct_2(X21,X18,X19)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ r2_hidden(X20,X18)
      | X19 = k1_xboole_0
      | r2_hidden(k1_funct_1(X21,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_15,negated_conjecture,(
    ! [X24] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk3_0,k9_setfam_1(esk3_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k9_setfam_1(esk3_0))))
      & ( r2_hidden(esk5_1(X24),esk3_0)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) )
      & ( k11_relat_1(X24,esk5_1(X24)) != k1_funct_1(esk4_0,esk5_1(X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

fof(c_0_16,plain,(
    ! [X7] : k9_setfam_1(X7) = k1_zfmisc_1(X7) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

cnf(c_0_17,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k9_setfam_1(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,k9_setfam_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_23,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(k1_funct_1(X2,X3),X1)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_2(X2,X4,X1)
    | ~ v1_funct_1(X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_zfmisc_1(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X8,X9,X12] :
      ( ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X8),k2_subset_1(X8))))
        | m1_subset_1(esk1_2(X8,X9),X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,k9_setfam_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,k9_setfam_1(X8)))) )
      & ( ~ m1_subset_1(X12,X8)
        | ~ r2_hidden(X12,k2_subset_1(X8))
        | k11_relat_1(esk2_2(X8,X9),X12) = k1_funct_1(X9,X12)
        | m1_subset_1(esk1_2(X8,X9),X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,k9_setfam_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,k9_setfam_1(X8)))) )
      & ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X8),k2_subset_1(X8))))
        | r2_hidden(esk1_2(X8,X9),k2_subset_1(X8))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,k9_setfam_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,k9_setfam_1(X8)))) )
      & ( ~ m1_subset_1(X12,X8)
        | ~ r2_hidden(X12,k2_subset_1(X8))
        | k11_relat_1(esk2_2(X8,X9),X12) = k1_funct_1(X9,X12)
        | r2_hidden(esk1_2(X8,X9),k2_subset_1(X8))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,k9_setfam_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,k9_setfam_1(X8)))) )
      & ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X8),k2_subset_1(X8))))
        | ~ r1_tarski(k1_funct_1(X9,esk1_2(X8,X9)),k2_subset_1(X8))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,k9_setfam_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,k9_setfam_1(X8)))) )
      & ( ~ m1_subset_1(X12,X8)
        | ~ r2_hidden(X12,k2_subset_1(X8))
        | k11_relat_1(esk2_2(X8,X9),X12) = k1_funct_1(X9,X12)
        | ~ r1_tarski(k1_funct_1(X9,esk1_2(X8,X9)),k2_subset_1(X8))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X8,k9_setfam_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,k9_setfam_1(X8)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_relset_1__e2_192__funct_2])])])])])).

fof(c_0_28,plain,(
    ! [X5] : k2_subset_1(X5) = X5 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | r2_hidden(k1_funct_1(esk4_0,X1),k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( k11_relat_1(esk2_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | r2_hidden(esk1_2(X2,X3),k2_subset_1(X2))
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k2_subset_1(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,k9_setfam_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k9_setfam_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | ~ r1_tarski(k1_funct_1(X2,esk1_2(X1,X2)),k2_subset_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | m1_subset_1(k1_funct_1(esk4_0,X1),k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k11_relat_1(esk2_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k2_subset_1(X2))
    | ~ r1_tarski(k1_funct_1(X3,esk1_2(X2,X3)),k2_subset_1(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,k9_setfam_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k9_setfam_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k11_relat_1(esk2_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | r2_hidden(esk1_2(X2,X3),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_2(X3,X2,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_zfmisc_1(X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_20]),c_0_20])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | r2_hidden(esk1_2(X1,X2),k2_subset_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_funct_1(X2,esk1_2(X1,X2)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_33]),c_0_33]),c_0_33]),c_0_20]),c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | r1_tarski(k1_funct_1(esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( k11_relat_1(esk2_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_2(X3,X2,k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_funct_1(X3,esk1_2(X2,X3)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_zfmisc_1(X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_33]),c_0_33]),c_0_20]),c_0_20])).

cnf(c_0_43,plain,
    ( k11_relat_1(esk2_2(X1,X2),X3) = k1_funct_1(X2,X3)
    | r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(X1))))
    | ~ v1_funct_2(X2,X1,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( k11_relat_1(X1,esk5_1(X1)) != k1_funct_1(esk4_0,esk5_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_33]),c_0_33]),c_0_33]),c_0_20]),c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | m1_subset_1(esk2_2(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | ~ r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_47,plain,
    ( k11_relat_1(esk2_2(X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r1_tarski(k1_funct_1(X2,esk1_2(X1,X2)),X1)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(X1))))
    | ~ v1_funct_2(X2,X1,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( k11_relat_1(esk2_2(esk3_0,esk4_0),X1) = k1_funct_1(esk4_0,X1)
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk3_0)
    | k11_relat_1(esk2_2(esk3_0,X1),esk5_1(esk2_2(esk3_0,X1))) != k1_funct_1(esk4_0,esk5_1(esk2_2(esk3_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_zfmisc_1(esk3_0))))
    | ~ v1_funct_2(X1,esk3_0,k1_zfmisc_1(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | k11_relat_1(esk2_2(esk3_0,esk4_0),esk5_1(esk2_2(esk3_0,esk4_0))) != k1_funct_1(esk4_0,esk5_1(esk2_2(esk3_0,esk4_0)))
    | ~ r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k11_relat_1(esk2_2(esk3_0,esk4_0),X1) = k1_funct_1(esk4_0,X1)
    | k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_24]),c_0_25]),c_0_26])]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | ~ r2_hidden(esk5_1(esk2_2(esk3_0,esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_1(X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | ~ r2_hidden(esk5_1(esk2_2(esk3_0,esk4_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | r2_hidden(esk5_1(esk2_2(esk3_0,esk4_0)),esk3_0)
    | ~ r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_1(esk2_2(esk3_0,X1)),esk3_0)
    | r2_hidden(esk1_2(esk3_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_zfmisc_1(esk3_0))))
    | ~ v1_funct_2(X1,esk3_0,k1_zfmisc_1(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

fof(c_0_57,plain,(
    ! [X6] : ~ v1_xboole_0(k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_58,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0
    | ~ r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_24]),c_0_25]),c_0_26])]),c_0_52])).

cnf(c_0_60,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
