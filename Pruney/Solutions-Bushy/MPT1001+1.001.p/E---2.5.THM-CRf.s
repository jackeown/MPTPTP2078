%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1001+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:33 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 412 expanded)
%              Number of clauses        :   35 ( 177 expanded)
%              Number of leaves         :    9 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 (1519 expanded)
%              Number of equality atoms :   51 ( 532 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & k8_relset_1(X1,X2,X3,k1_tarski(X4)) = k1_xboole_0 )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t143_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & k10_relat_1(X2,k1_tarski(X3)) = k1_xboole_0 )
       => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & k8_relset_1(X1,X2,X3,k1_tarski(X4)) = k1_xboole_0 )
        <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t49_funct_2])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k2_relset_1(X13,X14,X15) = k2_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_11,negated_conjecture,(
    ! [X31] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( r2_hidden(esk5_0,esk3_0)
        | k2_relset_1(esk2_0,esk3_0,esk4_0) != esk3_0 )
      & ( k8_relset_1(esk2_0,esk3_0,esk4_0,k1_tarski(esk5_0)) = k1_xboole_0
        | k2_relset_1(esk2_0,esk3_0,esk4_0) != esk3_0 )
      & ( ~ r2_hidden(X31,esk3_0)
        | k8_relset_1(esk2_0,esk3_0,esk4_0,k1_tarski(X31)) != k1_xboole_0
        | k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).

cnf(c_0_12,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k8_relset_1(X16,X17,X18,X19) = k10_relat_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_15,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | m1_subset_1(k2_relset_1(X10,X11,X12),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_17,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ r2_hidden(X1,esk3_0)
    | k8_relset_1(esk2_0,esk3_0,esk4_0,k1_tarski(X1)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ( ~ r2_hidden(X20,k2_relat_1(X21))
        | k10_relat_1(X21,k1_tarski(X20)) != k1_xboole_0
        | ~ v1_relat_1(X21) )
      & ( k10_relat_1(X21,k1_tarski(X20)) = k1_xboole_0
        | r2_hidden(X20,k2_relat_1(X21))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( ( r2_hidden(esk1_2(X22,X23),X22)
        | r1_tarski(X22,k2_relat_1(X23))
        | ~ v1_relat_1(X23) )
      & ( k10_relat_1(X23,k1_tarski(esk1_2(X22,X23))) = k1_xboole_0
        | r1_tarski(X22,k2_relat_1(X23))
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_funct_1])])])])).

cnf(c_0_25,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0
    | k8_relset_1(esk2_0,esk3_0,esk4_0,k1_tarski(X1)) != k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k8_relset_1(esk2_0,esk3_0,esk4_0,X1) = k10_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_13])).

cnf(c_0_27,plain,
    ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

fof(c_0_29,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_13])])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,k1_tarski(esk1_2(X2,X1))) = k1_xboole_0
    | r1_tarski(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0
    | k10_relat_1(esk4_0,k1_tarski(X1)) != k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k8_relset_1(esk2_0,esk3_0,esk4_0,k1_tarski(esk5_0)) = k1_xboole_0
    | k2_relset_1(esk2_0,esk3_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_tarski(esk1_2(X1,esk4_0))) = k1_xboole_0
    | r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0
    | r2_hidden(X1,k2_relat_1(esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(X1,esk4_0),X1)
    | r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0
    | ~ r1_tarski(esk3_0,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k8_relset_1(esk2_0,esk3_0,esk4_0,k1_tarski(esk5_0)) = k1_xboole_0
    | k2_relat_1(esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | k2_relset_1(esk2_0,esk3_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk4_0))
    | ~ r2_hidden(esk1_2(X1,esk4_0),k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28])])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0
    | r2_hidden(esk1_2(esk3_0,esk4_0),k2_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_tarski(esk5_0)) = k1_xboole_0
    | k2_relat_1(esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | k2_relat_1(esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(esk4_0) != esk3_0
    | ~ r2_hidden(esk5_0,k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_48]),c_0_28])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50]),c_0_50])]),c_0_52])]),
    [proof]).

%------------------------------------------------------------------------------
