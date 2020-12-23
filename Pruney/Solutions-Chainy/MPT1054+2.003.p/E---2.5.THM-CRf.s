%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:16 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 367 expanded)
%              Number of clauses        :   48 ( 162 expanded)
%              Number of leaves         :   21 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  170 ( 547 expanded)
%              Number of equality atoms :   66 ( 331 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t171_funct_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t217_relat_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1) )
         => v4_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(t164_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_21,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X39,X40] : k5_relat_1(k6_relat_1(X40),k6_relat_1(X39)) = k6_relat_1(k3_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X31] :
      ( k1_relat_1(k6_relat_1(X31)) = X31
      & k2_relat_1(k6_relat_1(X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_28,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_34,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k7_relat_1(X33,X32) = k5_relat_1(k6_relat_1(X32),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_35,plain,(
    ! [X34] :
      ( v1_relat_1(k6_relat_1(X34))
      & v4_relat_1(k6_relat_1(X34),X34)
      & v5_relat_1(k6_relat_1(X34),X34) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

fof(c_0_36,plain,(
    ! [X5,X6] : k2_tarski(X5,X6) = k2_tarski(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_37,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k2_relat_1(k7_relat_1(X25,X24)) = k9_relat_1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_43,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t171_funct_2])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_25]),c_0_25]),c_0_30]),c_0_30])).

cnf(c_0_46,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_39])])).

fof(c_0_47,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | r1_tarski(X14,X12)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r1_tarski(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r2_hidden(esk1_2(X16,X17),X17)
        | ~ r1_tarski(esk1_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) )
      & ( r2_hidden(esk1_2(X16,X17),X17)
        | r1_tarski(esk1_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_48,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

fof(c_0_50,plain,(
    ! [X19] : ~ v1_xboole_0(k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_51,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ v4_relat_1(X27,X26)
      | X27 = k7_relat_1(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_52,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_45]),c_0_33])).

cnf(c_0_53,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_46])).

fof(c_0_54,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(X28,X29)
      | ~ v1_relat_1(X30)
      | ~ v4_relat_1(X30,X28)
      | v4_relat_1(X30,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t217_relat_1])])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_59,plain,(
    ! [X46] : k6_partfun1(X46) = k6_relat_1(X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_60,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k8_relset_1(X41,X42,X43,X44) = k10_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_61,plain,(
    ! [X45] : m1_subset_1(k6_relat_1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_62,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_38]),c_0_53]),c_0_39])])).

cnf(c_0_64,plain,
    ( v4_relat_1(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_68,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_71,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v1_funct_1(X38)
      | ~ r1_tarski(X37,k1_relat_1(X38))
      | ~ v2_funct_1(X38)
      | k10_relat_1(X38,k9_relat_1(X38,X37)) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).

cnf(c_0_72,plain,
    ( k9_relat_1(X1,X2) = k2_relat_1(X1)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_62])).

cnf(c_0_73,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_63]),c_0_63])).

fof(c_0_74,plain,(
    ! [X36] :
      ( v1_relat_1(k6_relat_1(X36))
      & v2_funct_1(k6_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_75,plain,(
    ! [X35] :
      ( v1_relat_1(k6_relat_1(X35))
      & v1_funct_1(k6_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_76,plain,
    ( v4_relat_1(k6_relat_1(X1),X2)
    | ~ v4_relat_1(k6_relat_1(X1),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( k8_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_79,plain,
    ( k8_relset_1(X1,X1,k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = X2
    | ~ v4_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_31]),c_0_39])])).

cnf(c_0_82,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_85,negated_conjecture,
    ( v4_relat_1(k6_relat_1(X1),esk2_0)
    | ~ v4_relat_1(k6_relat_1(X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_87,negated_conjecture,
    ( k10_relat_1(k6_relat_1(esk2_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X2
    | ~ v4_relat_1(k6_relat_1(X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_83]),c_0_39]),c_0_84])])).

cnf(c_0_89,negated_conjecture,
    ( v4_relat_1(k6_relat_1(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:10:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.12/0.40  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.027 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.40  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.12/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.12/0.40  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.12/0.40  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.12/0.40  fof(t171_funct_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 0.12/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.40  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.12/0.40  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.12/0.40  fof(t217_relat_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v4_relat_1(X3,X1))=>v4_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 0.12/0.40  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.12/0.40  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.12/0.40  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.12/0.40  fof(t164_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 0.12/0.40  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.12/0.40  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.12/0.40  fof(c_0_21, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.40  fof(c_0_22, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.40  fof(c_0_23, plain, ![X39, X40]:k5_relat_1(k6_relat_1(X40),k6_relat_1(X39))=k6_relat_1(k3_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.12/0.40  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.40  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.40  fof(c_0_26, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.40  fof(c_0_27, plain, ![X31]:(k1_relat_1(k6_relat_1(X31))=X31&k2_relat_1(k6_relat_1(X31))=X31), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.40  cnf(c_0_28, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.40  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.40  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.40  cnf(c_0_31, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_32, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.12/0.40  cnf(c_0_33, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.40  fof(c_0_34, plain, ![X32, X33]:(~v1_relat_1(X33)|k7_relat_1(X33,X32)=k5_relat_1(k6_relat_1(X32),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.12/0.40  fof(c_0_35, plain, ![X34]:((v1_relat_1(k6_relat_1(X34))&v4_relat_1(k6_relat_1(X34),X34))&v5_relat_1(k6_relat_1(X34),X34)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.12/0.40  fof(c_0_36, plain, ![X5, X6]:k2_tarski(X5,X6)=k2_tarski(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.40  cnf(c_0_37, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.40  cnf(c_0_38, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.40  cnf(c_0_39, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.40  fof(c_0_40, plain, ![X24, X25]:(~v1_relat_1(X25)|k2_relat_1(k7_relat_1(X25,X24))=k9_relat_1(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.12/0.40  cnf(c_0_41, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.40  cnf(c_0_42, plain, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.12/0.40  cnf(c_0_43, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.40  fof(c_0_44, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t171_funct_2])).
% 0.12/0.40  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_25]), c_0_25]), c_0_30]), c_0_30])).
% 0.12/0.40  cnf(c_0_46, plain, (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_39])])).
% 0.12/0.40  fof(c_0_47, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|r1_tarski(X14,X12)|X13!=k1_zfmisc_1(X12))&(~r1_tarski(X15,X12)|r2_hidden(X15,X13)|X13!=k1_zfmisc_1(X12)))&((~r2_hidden(esk1_2(X16,X17),X17)|~r1_tarski(esk1_2(X16,X17),X16)|X17=k1_zfmisc_1(X16))&(r2_hidden(esk1_2(X16,X17),X17)|r1_tarski(esk1_2(X16,X17),X16)|X17=k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.40  fof(c_0_48, plain, ![X22, X23]:(~m1_subset_1(X22,X23)|(v1_xboole_0(X23)|r2_hidden(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.40  fof(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0)!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 0.12/0.40  fof(c_0_50, plain, ![X19]:~v1_xboole_0(k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.12/0.40  fof(c_0_51, plain, ![X26, X27]:(~v1_relat_1(X27)|~v4_relat_1(X27,X26)|X27=k7_relat_1(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.12/0.40  cnf(c_0_52, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_45]), c_0_33])).
% 0.12/0.40  cnf(c_0_53, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_46])).
% 0.12/0.40  fof(c_0_54, plain, ![X28, X29, X30]:(~r1_tarski(X28,X29)|(~v1_relat_1(X30)|~v4_relat_1(X30,X28)|v4_relat_1(X30,X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t217_relat_1])])])).
% 0.12/0.40  cnf(c_0_55, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.40  cnf(c_0_56, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.40  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.40  cnf(c_0_58, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.40  fof(c_0_59, plain, ![X46]:k6_partfun1(X46)=k6_relat_1(X46), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.12/0.40  fof(c_0_60, plain, ![X41, X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k8_relset_1(X41,X42,X43,X44)=k10_relat_1(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.12/0.40  fof(c_0_61, plain, ![X45]:m1_subset_1(k6_relat_1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.12/0.40  cnf(c_0_62, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.40  cnf(c_0_63, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_38]), c_0_53]), c_0_39])])).
% 0.12/0.40  cnf(c_0_64, plain, (v4_relat_1(X3,X2)|~r1_tarski(X1,X2)|~v1_relat_1(X3)|~v4_relat_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.12/0.40  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_55])).
% 0.12/0.40  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.12/0.40  cnf(c_0_67, negated_conjecture, (k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.40  cnf(c_0_68, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.40  cnf(c_0_69, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.40  cnf(c_0_70, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.40  fof(c_0_71, plain, ![X37, X38]:(~v1_relat_1(X38)|~v1_funct_1(X38)|(~r1_tarski(X37,k1_relat_1(X38))|~v2_funct_1(X38)|k10_relat_1(X38,k9_relat_1(X38,X37))=X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).
% 0.12/0.40  cnf(c_0_72, plain, (k9_relat_1(X1,X2)=k2_relat_1(X1)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_62])).
% 0.12/0.40  cnf(c_0_73, plain, (k9_relat_1(k6_relat_1(X1),X2)=k9_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_63]), c_0_63])).
% 0.12/0.40  fof(c_0_74, plain, ![X36]:(v1_relat_1(k6_relat_1(X36))&v2_funct_1(k6_relat_1(X36))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.12/0.40  fof(c_0_75, plain, ![X35]:(v1_relat_1(k6_relat_1(X35))&v1_funct_1(k6_relat_1(X35))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.12/0.40  cnf(c_0_76, plain, (v4_relat_1(k6_relat_1(X1),X2)|~v4_relat_1(k6_relat_1(X1),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_64, c_0_39])).
% 0.12/0.40  cnf(c_0_77, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.12/0.40  cnf(c_0_78, negated_conjecture, (k8_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),esk3_0)!=esk3_0), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.40  cnf(c_0_79, plain, (k8_relset_1(X1,X1,k6_relat_1(X1),X2)=k10_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.12/0.40  cnf(c_0_80, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.12/0.40  cnf(c_0_81, plain, (k9_relat_1(k6_relat_1(X1),X2)=X2|~v4_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_31]), c_0_39])])).
% 0.12/0.40  cnf(c_0_82, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.12/0.40  cnf(c_0_83, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.12/0.40  cnf(c_0_84, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_85, negated_conjecture, (v4_relat_1(k6_relat_1(X1),esk2_0)|~v4_relat_1(k6_relat_1(X1),esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.12/0.40  cnf(c_0_86, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.40  cnf(c_0_87, negated_conjecture, (k10_relat_1(k6_relat_1(esk2_0),esk3_0)!=esk3_0), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.12/0.40  cnf(c_0_88, plain, (k10_relat_1(k6_relat_1(X1),X2)=X2|~v4_relat_1(k6_relat_1(X2),X1)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_83]), c_0_39]), c_0_84])])).
% 0.12/0.40  cnf(c_0_89, negated_conjecture, (v4_relat_1(k6_relat_1(esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.12/0.40  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_77])]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 91
% 0.12/0.40  # Proof object clause steps            : 48
% 0.12/0.40  # Proof object formula steps           : 43
% 0.12/0.40  # Proof object conjectures             : 12
% 0.12/0.40  # Proof object clause conjectures      : 9
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 24
% 0.12/0.40  # Proof object initial formulas used   : 21
% 0.12/0.40  # Proof object generating inferences   : 16
% 0.12/0.40  # Proof object simplifying inferences  : 33
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 21
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 30
% 0.12/0.40  # Removed in clause preprocessing      : 4
% 0.12/0.40  # Initial clauses in saturation        : 26
% 0.12/0.40  # Processed clauses                    : 410
% 0.12/0.40  # ...of these trivial                  : 11
% 0.12/0.40  # ...subsumed                          : 164
% 0.12/0.40  # ...remaining for further processing  : 235
% 0.12/0.40  # Other redundant clauses eliminated   : 2
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 0
% 0.12/0.40  # Backward-rewritten                   : 60
% 0.12/0.40  # Generated clauses                    : 1624
% 0.12/0.40  # ...of the previous two non-trivial   : 1354
% 0.12/0.40  # Contextual simplify-reflections      : 0
% 0.12/0.40  # Paramodulations                      : 1620
% 0.12/0.40  # Factorizations                       : 2
% 0.12/0.40  # Equation resolutions                 : 2
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 149
% 0.12/0.40  #    Positive orientable unit clauses  : 57
% 0.12/0.40  #    Positive unorientable unit clauses: 3
% 0.12/0.40  #    Negative unit clauses             : 2
% 0.12/0.40  #    Non-unit-clauses                  : 87
% 0.12/0.40  # Current number of unprocessed clauses: 871
% 0.12/0.40  # ...number of literals in the above   : 1823
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 88
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 4394
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 3729
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 154
% 0.12/0.40  # Unit Clause-clause subsumption calls : 163
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 98
% 0.12/0.40  # BW rewrite match successes           : 67
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 26243
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.063 s
% 0.12/0.40  # System time              : 0.002 s
% 0.12/0.40  # Total time               : 0.065 s
% 0.12/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
