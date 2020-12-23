%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 342 expanded)
%              Number of clauses        :   43 ( 150 expanded)
%              Number of leaves         :   20 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 471 expanded)
%              Number of equality atoms :   62 ( 314 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
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

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(t67_funct_1,axiom,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_20,plain,(
    ! [X12,X13] : k1_setfam_1(k2_tarski(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X31,X32] : k5_relat_1(k6_relat_1(X32),k6_relat_1(X31)) = k6_relat_1(k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X23] :
      ( k1_relat_1(k6_relat_1(X23)) = X23
      & k2_relat_1(k6_relat_1(X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_27,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_33,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k7_relat_1(X25,X24) = k5_relat_1(k6_relat_1(X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_34,plain,(
    ! [X26] :
      ( v1_relat_1(k6_relat_1(X26))
      & v4_relat_1(k6_relat_1(X26),X26)
      & v5_relat_1(k6_relat_1(X26),X26) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

fof(c_0_35,plain,(
    ! [X5,X6] : k2_tarski(X5,X6) = k2_tarski(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_36,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k2_relat_1(k7_relat_1(X17,X16)) = k9_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_42,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t171_funct_2])).

fof(c_0_44,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ v2_funct_1(X30)
      | k10_relat_1(X30,X29) = k9_relat_1(k2_funct_1(X30),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

fof(c_0_45,plain,(
    ! [X33] : k2_funct_1(k6_relat_1(X33)) = k6_relat_1(X33) ),
    inference(variable_rename,[status(thm)],[t67_funct_1])).

fof(c_0_46,plain,(
    ! [X28] :
      ( v1_relat_1(k6_relat_1(X28))
      & v2_funct_1(k6_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_47,plain,(
    ! [X27] :
      ( v1_relat_1(k6_relat_1(X27))
      & v1_funct_1(k6_relat_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_24]),c_0_24]),c_0_29]),c_0_29])).

cnf(c_0_49,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_38])])).

fof(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

fof(c_0_51,plain,(
    ! [X39] : k6_partfun1(X39) = k6_relat_1(X39) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_52,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k8_relset_1(X34,X35,X36,X37) = k10_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_53,plain,(
    ! [X38] : m1_subset_1(k6_relat_1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_54,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_58,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ v4_relat_1(X19,X18)
      | X19 = k7_relat_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_59,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_48]),c_0_32])).

cnf(c_0_60,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_49])).

fof(c_0_61,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ v1_relat_1(X22)
      | ~ v4_relat_1(X22,X20)
      | v4_relat_1(X22,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t217_relat_1])])])).

fof(c_0_62,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_63,negated_conjecture,
    ( k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_38])])).

cnf(c_0_68,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_37]),c_0_60]),c_0_38])])).

cnf(c_0_70,plain,
    ( v4_relat_1(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_74,negated_conjecture,
    ( k8_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),esk2_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_75,plain,
    ( k8_relset_1(X1,X1,k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_76,plain,
    ( k9_relat_1(X1,X2) = k2_relat_1(X1)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_68])).

cnf(c_0_77,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_69]),c_0_69])).

cnf(c_0_78,plain,
    ( v4_relat_1(k6_relat_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_38])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk1_0),esk2_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = X2
    | ~ v4_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_30]),c_0_38])])).

cnf(c_0_82,negated_conjecture,
    ( v4_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.39  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.39  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.13/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.39  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.39  fof(t171_funct_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 0.13/0.39  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 0.13/0.39  fof(t67_funct_1, axiom, ![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 0.13/0.39  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.13/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.13/0.39  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.13/0.39  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.13/0.39  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.13/0.39  fof(t217_relat_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v4_relat_1(X3,X1))=>v4_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(c_0_20, plain, ![X12, X13]:k1_setfam_1(k2_tarski(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.39  fof(c_0_21, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X31, X32]:k5_relat_1(k6_relat_1(X32),k6_relat_1(X31))=k6_relat_1(k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.13/0.39  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  fof(c_0_25, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_26, plain, ![X23]:(k1_relat_1(k6_relat_1(X23))=X23&k2_relat_1(k6_relat_1(X23))=X23), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.39  cnf(c_0_27, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.39  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_30, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_31, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.13/0.39  cnf(c_0_32, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  fof(c_0_33, plain, ![X24, X25]:(~v1_relat_1(X25)|k7_relat_1(X25,X24)=k5_relat_1(k6_relat_1(X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.39  fof(c_0_34, plain, ![X26]:((v1_relat_1(k6_relat_1(X26))&v4_relat_1(k6_relat_1(X26),X26))&v5_relat_1(k6_relat_1(X26),X26)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.13/0.39  fof(c_0_35, plain, ![X5, X6]:k2_tarski(X5,X6)=k2_tarski(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.39  cnf(c_0_36, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.39  cnf(c_0_37, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  cnf(c_0_38, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  fof(c_0_39, plain, ![X16, X17]:(~v1_relat_1(X17)|k2_relat_1(k7_relat_1(X17,X16))=k9_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.39  cnf(c_0_40, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_41, plain, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.13/0.39  cnf(c_0_42, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  fof(c_0_43, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t171_funct_2])).
% 0.13/0.39  fof(c_0_44, plain, ![X29, X30]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~v2_funct_1(X30)|k10_relat_1(X30,X29)=k9_relat_1(k2_funct_1(X30),X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.13/0.39  fof(c_0_45, plain, ![X33]:k2_funct_1(k6_relat_1(X33))=k6_relat_1(X33), inference(variable_rename,[status(thm)],[t67_funct_1])).
% 0.13/0.39  fof(c_0_46, plain, ![X28]:(v1_relat_1(k6_relat_1(X28))&v2_funct_1(k6_relat_1(X28))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.13/0.39  fof(c_0_47, plain, ![X27]:(v1_relat_1(k6_relat_1(X27))&v1_funct_1(k6_relat_1(X27))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.39  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_24]), c_0_24]), c_0_29]), c_0_29])).
% 0.13/0.39  cnf(c_0_49, plain, (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_38])])).
% 0.13/0.39  fof(c_0_50, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0)!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.13/0.39  fof(c_0_51, plain, ![X39]:k6_partfun1(X39)=k6_relat_1(X39), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.13/0.39  fof(c_0_52, plain, ![X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k8_relset_1(X34,X35,X36,X37)=k10_relat_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.13/0.39  fof(c_0_53, plain, ![X38]:m1_subset_1(k6_relat_1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.13/0.39  cnf(c_0_54, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_55, plain, (k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.39  cnf(c_0_56, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_57, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.39  fof(c_0_58, plain, ![X18, X19]:(~v1_relat_1(X19)|~v4_relat_1(X19,X18)|X19=k7_relat_1(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.13/0.39  cnf(c_0_59, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_48]), c_0_32])).
% 0.13/0.39  cnf(c_0_60, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_49])).
% 0.13/0.39  fof(c_0_61, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|(~v1_relat_1(X22)|~v4_relat_1(X22,X20)|v4_relat_1(X22,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t217_relat_1])])])).
% 0.13/0.39  fof(c_0_62, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.39  cnf(c_0_64, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_65, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_66, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  cnf(c_0_67, plain, (k10_relat_1(k6_relat_1(X1),X2)=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_38])])).
% 0.13/0.39  cnf(c_0_68, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.39  cnf(c_0_69, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_37]), c_0_60]), c_0_38])])).
% 0.13/0.39  cnf(c_0_70, plain, (v4_relat_1(X3,X2)|~r1_tarski(X1,X2)|~v1_relat_1(X3)|~v4_relat_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.39  cnf(c_0_71, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (k8_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),esk2_0)!=esk2_0), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.39  cnf(c_0_75, plain, (k8_relset_1(X1,X1,k6_relat_1(X1),X2)=k9_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.13/0.39  cnf(c_0_76, plain, (k9_relat_1(X1,X2)=k2_relat_1(X1)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_68])).
% 0.13/0.39  cnf(c_0_77, plain, (k9_relat_1(k6_relat_1(X1),X2)=k9_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_69]), c_0_69])).
% 0.13/0.39  cnf(c_0_78, plain, (v4_relat_1(k6_relat_1(X1),X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_38])])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (k9_relat_1(k6_relat_1(esk1_0),esk2_0)!=esk2_0), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.39  cnf(c_0_81, plain, (k9_relat_1(k6_relat_1(X1),X2)=X2|~v4_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_30]), c_0_38])])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (v4_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 84
% 0.13/0.39  # Proof object clause steps            : 43
% 0.13/0.39  # Proof object formula steps           : 41
% 0.13/0.39  # Proof object conjectures             : 10
% 0.13/0.39  # Proof object clause conjectures      : 7
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 22
% 0.13/0.39  # Proof object initial formulas used   : 20
% 0.13/0.39  # Proof object generating inferences   : 14
% 0.13/0.39  # Proof object simplifying inferences  : 32
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 20
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 27
% 0.13/0.39  # Removed in clause preprocessing      : 4
% 0.13/0.39  # Initial clauses in saturation        : 23
% 0.13/0.39  # Processed clauses                    : 173
% 0.13/0.39  # ...of these trivial                  : 7
% 0.13/0.39  # ...subsumed                          : 31
% 0.13/0.39  # ...remaining for further processing  : 135
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 34
% 0.13/0.39  # Generated clauses                    : 619
% 0.13/0.39  # ...of the previous two non-trivial   : 516
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 619
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
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
% 0.13/0.39  # Current number of processed clauses  : 78
% 0.13/0.39  #    Positive orientable unit clauses  : 39
% 0.13/0.39  #    Positive unorientable unit clauses: 2
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 36
% 0.13/0.39  # Current number of unprocessed clauses: 324
% 0.13/0.39  # ...number of literals in the above   : 487
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 61
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 320
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 266
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 33
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 26
% 0.13/0.39  # BW rewrite match successes           : 20
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 8263
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.034 s
% 0.13/0.39  # System time              : 0.008 s
% 0.13/0.39  # Total time               : 0.042 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
