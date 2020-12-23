%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:25 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 226 expanded)
%              Number of clauses        :   41 (  93 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  178 (1010 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t48_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X33,X34,X35] :
      ( ( X34 = k1_xboole_0
        | k8_relset_1(X33,X34,X35,X34) = X33
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_xboole_0
        | k8_relset_1(X33,X34,X35,X34) = X33
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).

fof(c_0_18,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k8_relset_1(X29,X30,X31,X32) = k10_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_19,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k7_relset_1(X25,X26,X27,X28) = k9_relat_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_20,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | r1_tarski(k10_relat_1(X19,X18),k1_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,X1) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( k7_relset_1(esk1_0,esk2_0,esk3_0,X1) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

fof(c_0_35,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | r1_tarski(k9_relat_1(X21,k10_relat_1(X21,X20)),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_36,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk3_0,esk2_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_40,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(k9_relat_1(X17,X15),k9_relat_1(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)
    | r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_30])])).

fof(c_0_51,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ r1_tarski(X22,k1_relat_1(X24))
      | ~ r1_tarski(k9_relat_1(X24,X22),X23)
      | r1_tarski(X22,k10_relat_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k10_relat_1(esk3_0,esk5_0)))
    | r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk4_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_30]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk4_0,k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_26]),c_0_30])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_60]),c_0_62])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.21/0.43  # and selection function SelectNewComplexAHP.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.027 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t172_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 0.21/0.43  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.43  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.43  fof(t48_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 0.21/0.43  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.21/0.43  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.43  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.21/0.43  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.21/0.43  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.21/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.43  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.21/0.43  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.21/0.43  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.43  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t172_funct_2])).
% 0.21/0.43  fof(c_0_14, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.43  fof(c_0_15, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)))&(r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.21/0.43  fof(c_0_16, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.43  fof(c_0_17, plain, ![X33, X34, X35]:((X34=k1_xboole_0|k8_relset_1(X33,X34,X35,X34)=X33|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&(X33!=k1_xboole_0|k8_relset_1(X33,X34,X35,X34)=X33|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).
% 0.21/0.43  fof(c_0_18, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k8_relset_1(X29,X30,X31,X32)=k10_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.21/0.43  fof(c_0_19, plain, ![X25, X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k7_relset_1(X25,X26,X27,X28)=k9_relat_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.43  fof(c_0_20, plain, ![X18, X19]:(~v1_relat_1(X19)|r1_tarski(k10_relat_1(X19,X18),k1_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.21/0.43  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_23, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.43  cnf(c_0_24, plain, (X1=k1_xboole_0|k8_relset_1(X2,X1,X3,X1)=X2|~v1_funct_1(X3)|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.43  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_27, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.43  cnf(c_0_28, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_29, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.43  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.21/0.43  cnf(c_0_31, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_25]), c_0_26])])).
% 0.21/0.43  cnf(c_0_32, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,X1)=k10_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.21/0.43  cnf(c_0_33, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_34, negated_conjecture, (k7_relset_1(esk1_0,esk2_0,esk3_0,X1)=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.21/0.43  fof(c_0_35, plain, ![X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|r1_tarski(k9_relat_1(X21,k10_relat_1(X21,X20)),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.21/0.43  fof(c_0_36, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.21/0.43  cnf(c_0_37, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.43  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk3_0,esk2_0)=esk1_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.43  fof(c_0_39, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.43  fof(c_0_40, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|(~r1_tarski(X15,X16)|r1_tarski(k9_relat_1(X17,X15),k9_relat_1(X17,X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.21/0.43  cnf(c_0_41, negated_conjecture, (r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))|r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.43  cnf(c_0_42, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.43  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.43  cnf(c_0_44, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.43  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.43  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_47, negated_conjecture, (~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_48, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.43  cnf(c_0_49, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_41, c_0_32])).
% 0.21/0.43  cnf(c_0_50, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_30])])).
% 0.21/0.43  fof(c_0_51, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|~v1_funct_1(X24)|(~r1_tarski(X22,k1_relat_1(X24))|~r1_tarski(k9_relat_1(X24,X22),X23)|r1_tarski(X22,k10_relat_1(X24,X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.21/0.43  cnf(c_0_52, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.43  cnf(c_0_53, negated_conjecture, (r1_tarski(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.43  cnf(c_0_54, negated_conjecture, (~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))|~r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_47, c_0_34])).
% 0.21/0.43  cnf(c_0_55, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k10_relat_1(esk3_0,esk5_0)))|r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.43  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 0.21/0.43  cnf(c_0_57, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.43  cnf(c_0_58, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk4_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.43  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))|~r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_54, c_0_32])).
% 0.21/0.43  cnf(c_0_60, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_30]), c_0_56])).
% 0.21/0.43  cnf(c_0_61, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk4_0,k10_relat_1(esk3_0,X1))|~r1_tarski(k9_relat_1(esk3_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_26]), c_0_30])])).
% 0.21/0.43  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.21/0.43  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_64, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_60]), c_0_62])).
% 0.21/0.43  cnf(c_0_65, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.43  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_65])]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 67
% 0.21/0.44  # Proof object clause steps            : 41
% 0.21/0.44  # Proof object formula steps           : 26
% 0.21/0.44  # Proof object conjectures             : 32
% 0.21/0.44  # Proof object clause conjectures      : 29
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 19
% 0.21/0.44  # Proof object initial formulas used   : 13
% 0.21/0.44  # Proof object generating inferences   : 15
% 0.21/0.44  # Proof object simplifying inferences  : 22
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 13
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 23
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 23
% 0.21/0.44  # Processed clauses                    : 696
% 0.21/0.44  # ...of these trivial                  : 5
% 0.21/0.44  # ...subsumed                          : 201
% 0.21/0.44  # ...remaining for further processing  : 490
% 0.21/0.44  # Other redundant clauses eliminated   : 1
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 5
% 0.21/0.44  # Backward-rewritten                   : 337
% 0.21/0.44  # Generated clauses                    : 1424
% 0.21/0.44  # ...of the previous two non-trivial   : 1370
% 0.21/0.44  # Contextual simplify-reflections      : 1
% 0.21/0.44  # Paramodulations                      : 1420
% 0.21/0.44  # Factorizations                       : 0
% 0.21/0.44  # Equation resolutions                 : 1
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 121
% 0.21/0.44  #    Positive orientable unit clauses  : 50
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 2
% 0.21/0.44  #    Non-unit-clauses                  : 69
% 0.21/0.44  # Current number of unprocessed clauses: 631
% 0.21/0.44  # ...number of literals in the above   : 1121
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 368
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 8656
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 6350
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 205
% 0.21/0.44  # Unit Clause-clause subsumption calls : 777
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 60
% 0.21/0.44  # BW rewrite match successes           : 7
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 27048
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.083 s
% 0.21/0.44  # System time              : 0.007 s
% 0.21/0.44  # Total time               : 0.091 s
% 0.21/0.44  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
