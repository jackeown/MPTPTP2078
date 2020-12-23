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
% DateTime   : Thu Dec  3 11:07:23 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 220 expanded)
%              Number of clauses        :   40 (  90 expanded)
%              Number of leaves         :   12 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 (1086 expanded)
%              Number of equality atoms :   42 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t172_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(X2))
                     => ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
                      <=> r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(X2))
                       => ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
                        <=> r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t172_funct_2])).

fof(c_0_13,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k7_relset_1(X25,X26,X27,X28) = k9_relat_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_14,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
      | ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) )
    & ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
      | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k8_relset_1(X29,X30,X31,X32) = k10_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_17,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_18,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r1_tarski(X16,k1_relat_1(X18))
      | ~ r1_tarski(k9_relat_1(X18,X16),X17)
      | r1_tarski(X16,k10_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_22,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( k7_relset_1(esk1_0,esk2_0,esk3_0,X1) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relset_1(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)
    | r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_34,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v1_funct_2(X35,X33,X34)
        | X33 = k1_relset_1(X33,X34,X35)
        | X34 = k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_relset_1(X33,X34,X35)
        | v1_funct_2(X35,X33,X34)
        | X34 = k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( ~ v1_funct_2(X35,X33,X34)
        | X33 = k1_relset_1(X33,X34,X35)
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_relset_1(X33,X34,X35)
        | v1_funct_2(X35,X33,X34)
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( ~ v1_funct_2(X35,X33,X34)
        | X35 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X35 != k1_xboole_0
        | v1_funct_2(X35,X33,X34)
        | X33 = k1_xboole_0
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,X2))
    | ~ r1_tarski(X1,k1_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk5_0)))
    | r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk5_0)))
    | ~ r1_tarski(esk4_0,k1_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_44,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_45,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(k9_relat_1(X13,X11),k9_relat_1(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_48,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_30]),c_0_31])])).

cnf(c_0_55,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k10_relat_1(esk3_0,esk5_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(k9_relat_1(esk3_0,esk4_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:57:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.14/0.40  # and selection function SelectNewComplexAHP.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.029 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t172_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 0.14/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.40  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.14/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.40  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.14/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.40  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.14/0.40  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.14/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.14/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t172_funct_2])).
% 0.14/0.40  fof(c_0_13, plain, ![X25, X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k7_relset_1(X25,X26,X27,X28)=k9_relat_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.40  fof(c_0_14, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)))&(r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.14/0.40  fof(c_0_15, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k8_relset_1(X29,X30,X31,X32)=k10_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.14/0.40  fof(c_0_16, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k1_relset_1(X22,X23,X24)=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.40  fof(c_0_17, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.40  cnf(c_0_18, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_20, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  fof(c_0_21, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r1_tarski(X16,k1_relat_1(X18))|~r1_tarski(k9_relat_1(X18,X16),X17)|r1_tarski(X16,k10_relat_1(X18,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.14/0.40  cnf(c_0_22, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_23, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  fof(c_0_24, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.40  cnf(c_0_25, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_26, negated_conjecture, (k7_relset_1(esk1_0,esk2_0,esk3_0,X1)=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.40  cnf(c_0_27, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,X1)=k10_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.14/0.40  cnf(c_0_28, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.40  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk3_0)=k1_relset_1(esk1_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.14/0.40  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.14/0.40  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.40  cnf(c_0_33, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.14/0.40  fof(c_0_34, plain, ![X33, X34, X35]:((((~v1_funct_2(X35,X33,X34)|X33=k1_relset_1(X33,X34,X35)|X34=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X33!=k1_relset_1(X33,X34,X35)|v1_funct_2(X35,X33,X34)|X34=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&((~v1_funct_2(X35,X33,X34)|X33=k1_relset_1(X33,X34,X35)|X33!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X33!=k1_relset_1(X33,X34,X35)|v1_funct_2(X35,X33,X34)|X33!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))))&((~v1_funct_2(X35,X33,X34)|X35=k1_xboole_0|X33=k1_xboole_0|X34!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X35!=k1_xboole_0|v1_funct_2(X35,X33,X34)|X33=k1_xboole_0|X34!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.40  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk3_0,X2))|~r1_tarski(X1,k1_relset_1(esk1_0,esk2_0,esk3_0))|~r1_tarski(k9_relat_1(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.14/0.40  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk5_0)))|r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.40  cnf(c_0_37, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.40  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.40  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk5_0)))|~r1_tarski(esk4_0,k1_relset_1(esk1_0,esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32])).
% 0.14/0.40  cnf(c_0_42, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_38])])).
% 0.14/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.40  fof(c_0_44, plain, ![X14, X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.14/0.40  fof(c_0_45, plain, ![X11, X12, X13]:(~v1_relat_1(X13)|(~r1_tarski(X11,X12)|r1_tarski(k9_relat_1(X13,X11),k9_relat_1(X13,X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.14/0.40  cnf(c_0_46, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k10_relat_1(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.14/0.40  cnf(c_0_47, negated_conjecture, (~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  fof(c_0_48, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.14/0.40  cnf(c_0_49, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.40  cnf(c_0_50, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.40  cnf(c_0_51, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_46])).
% 0.14/0.40  cnf(c_0_52, negated_conjecture, (~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))|~r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_47, c_0_26])).
% 0.14/0.40  cnf(c_0_53, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.40  cnf(c_0_54, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_30]), c_0_31])])).
% 0.14/0.40  cnf(c_0_55, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k10_relat_1(esk3_0,esk5_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.14/0.40  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))|~r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_52, c_0_27])).
% 0.14/0.40  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.14/0.40  cnf(c_0_58, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(k9_relat_1(esk3_0,esk4_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_55, c_0_31])).
% 0.14/0.40  cnf(c_0_59, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 0.14/0.40  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_61, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.14/0.40  cnf(c_0_62, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.40  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 64
% 0.14/0.40  # Proof object clause steps            : 40
% 0.14/0.40  # Proof object formula steps           : 24
% 0.14/0.40  # Proof object conjectures             : 31
% 0.14/0.40  # Proof object clause conjectures      : 28
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 19
% 0.14/0.40  # Proof object initial formulas used   : 12
% 0.14/0.40  # Proof object generating inferences   : 17
% 0.14/0.40  # Proof object simplifying inferences  : 18
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 12
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 26
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 26
% 0.14/0.40  # Processed clauses                    : 156
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 13
% 0.14/0.40  # ...remaining for further processing  : 143
% 0.14/0.40  # Other redundant clauses eliminated   : 5
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 0
% 0.14/0.40  # Backward-rewritten                   : 62
% 0.14/0.40  # Generated clauses                    : 216
% 0.14/0.40  # ...of the previous two non-trivial   : 248
% 0.14/0.40  # Contextual simplify-reflections      : 2
% 0.14/0.40  # Paramodulations                      : 212
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 5
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 51
% 0.14/0.40  #    Positive orientable unit clauses  : 15
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 1
% 0.14/0.40  #    Non-unit-clauses                  : 35
% 0.14/0.40  # Current number of unprocessed clauses: 96
% 0.14/0.40  # ...number of literals in the above   : 161
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 88
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 400
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 278
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 15
% 0.14/0.40  # Unit Clause-clause subsumption calls : 39
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 11
% 0.14/0.40  # BW rewrite match successes           : 3
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 5805
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.046 s
% 0.14/0.40  # System time              : 0.004 s
% 0.14/0.40  # Total time               : 0.050 s
% 0.14/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
