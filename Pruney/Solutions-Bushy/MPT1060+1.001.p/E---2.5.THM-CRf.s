%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1060+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:40 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  162 (8187 expanded)
%              Number of clauses        :  105 (3667 expanded)
%              Number of leaves         :   28 (2081 expanded)
%              Depth                    :   17
%              Number of atoms          :  297 (19740 expanded)
%              Number of equality atoms :  133 (8079 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t177_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X2))
         => ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
           => k3_subset_1(X1,k8_relset_1(X1,X2,X3,X4)) = k8_relset_1(X1,X2,X3,k3_subset_1(X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_2)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t137_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(t25_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(t46_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ( r1_xboole_0(X2,X3)
              & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

fof(t171_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(c_0_28,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_29,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_30,plain,(
    ! [X59,X60] :
      ( ( ~ m1_subset_1(X59,k1_zfmisc_1(X60))
        | r1_tarski(X59,X60) )
      & ( ~ r1_tarski(X59,X60)
        | m1_subset_1(X59,k1_zfmisc_1(X60)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X75,X76] : r1_xboole_0(k4_xboole_0(X75,X76),X76) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_34,plain,(
    ! [X67] : k4_xboole_0(k1_xboole_0,X67) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_35,plain,(
    ! [X56,X57] :
      ( ( k4_xboole_0(X56,X57) != k1_xboole_0
        | r1_tarski(X56,X57) )
      & ( ~ r1_tarski(X56,X57)
        | k4_xboole_0(X56,X57) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_38,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k3_xboole_0(X15,X16) = k1_xboole_0 )
      & ( k3_xboole_0(X15,X16) != k1_xboole_0
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X68,X69,X70] : k4_xboole_0(X68,k2_xboole_0(X69,X70)) = k3_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X68,X70)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_49,plain,(
    ! [X53] : k3_xboole_0(X53,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X2))
           => ( ( X2 = k1_xboole_0
               => X1 = k1_xboole_0 )
             => k3_subset_1(X1,k8_relset_1(X1,X2,X3,X4)) = k8_relset_1(X1,X2,X3,k3_subset_1(X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t177_funct_2])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_55,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k3_subset_1(X13,X14) = k4_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_52])).

fof(c_0_59,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_60,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & k3_subset_1(esk2_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)) != k8_relset_1(esk2_0,esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

fof(c_0_61,plain,(
    ! [X64,X65,X66] :
      ( ( X65 = k1_xboole_0
        | k8_relset_1(X64,X65,X66,X65) = X64
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( X64 != k1_xboole_0
        | k8_relset_1(X64,X65,X66,X65) = X64
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).

fof(c_0_62,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k8_relset_1(X36,X37,X38,X39) = k10_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_64,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_58])).

fof(c_0_67,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_68,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | k10_relat_1(X45,k3_xboole_0(X43,X44)) = k3_xboole_0(k10_relat_1(X45,X43),k10_relat_1(X45,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).

cnf(c_0_69,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_72,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | k4_subset_1(X51,X52,k3_subset_1(X51,X52)) = k2_subset_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).

fof(c_0_73,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | m1_subset_1(k3_subset_1(X19,X20),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_74,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,k3_subset_1(X31,X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_75,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | m1_subset_1(k8_relset_1(X21,X22,X23,X24),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_76,plain,(
    ! [X58] : k4_xboole_0(X58,k1_xboole_0) = X58 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_77,plain,(
    ! [X47,X48,X49] :
      ( ~ v1_relat_1(X49)
      | k10_relat_1(X49,k2_xboole_0(X47,X48)) = k2_xboole_0(k10_relat_1(X49,X47),k10_relat_1(X49,X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,X1) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_81,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_82,plain,(
    ! [X61,X62,X63] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(X61))
      | ~ m1_subset_1(X63,k1_zfmisc_1(X61))
      | ~ r1_xboole_0(X62,X63)
      | ~ r1_xboole_0(k3_subset_1(X61,X62),k3_subset_1(X61,X63))
      | X62 = k3_subset_1(X61,X63) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_subset_1])])])).

cnf(c_0_83,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),k4_xboole_0(k2_xboole_0(X1,X2),X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k3_subset_1(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_66])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_87,plain,
    ( k10_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = k3_subset_1(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_71])).

fof(c_0_90,plain,(
    ! [X46] :
      ( ~ v1_relat_1(X46)
      | k10_relat_1(X46,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_relat_1])])).

fof(c_0_91,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | k4_subset_1(X33,X34,X35) = k2_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_92,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_93,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_94,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_96,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_97,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_98,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_99,negated_conjecture,
    ( k8_relset_1(esk2_0,esk3_0,esk4_0,esk3_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_70])])).

cnf(c_0_100,negated_conjecture,
    ( k8_relset_1(esk2_0,esk3_0,esk4_0,X1) = k10_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_70])).

fof(c_0_101,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_102,plain,
    ( X1 = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(k3_subset_1(X2,X1),k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_103,plain,
    ( r1_xboole_0(k3_subset_1(k2_xboole_0(X1,X2),X1),k4_xboole_0(k2_xboole_0(X1,X2),X2)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_104,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k3_subset_1(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_85])).

cnf(c_0_105,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_86])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2)) = k10_relat_1(esk4_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_80])])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk3_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_89])).

cnf(c_0_108,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_109,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_110,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_32])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_71])).

cnf(c_0_112,negated_conjecture,
    ( k3_subset_1(esk3_0,k3_subset_1(esk3_0,esk5_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_71])).

fof(c_0_113,plain,(
    ! [X17] : m1_subset_1(k1_subset_1(X17),k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

cnf(c_0_114,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_95])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(k8_relset_1(esk2_0,esk3_0,esk4_0,X1),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_70])).

cnf(c_0_116,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_37]),c_0_47])).

cnf(c_0_117,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_97])).

cnf(c_0_118,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2)) = k10_relat_1(esk4_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_88])).

cnf(c_0_119,negated_conjecture,
    ( k10_relat_1(esk4_0,esk3_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

fof(c_0_121,plain,(
    ! [X30] : k2_xboole_0(X30,X30) = X30 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_122,plain,
    ( X1 = k3_subset_1(k2_xboole_0(X2,X3),X3)
    | ~ r1_xboole_0(k3_subset_1(k2_xboole_0(X2,X3),X1),k3_subset_1(k2_xboole_0(X2,X3),X3))
    | ~ r1_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_85])).

cnf(c_0_123,plain,
    ( r1_xboole_0(k3_subset_1(k2_xboole_0(X1,X2),X1),k3_subset_1(k2_xboole_0(X1,X2),X2)) ),
    inference(rw,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_124,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(esk4_0,X1),k10_relat_1(esk4_0,X2))
    | k10_relat_1(esk4_0,k3_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_125,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_107]),c_0_86])).

cnf(c_0_126,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_88])).

cnf(c_0_127,negated_conjecture,
    ( k4_subset_1(esk3_0,X1,esk5_0) = k2_xboole_0(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_71])).

cnf(c_0_128,negated_conjecture,
    ( k4_subset_1(esk3_0,k3_subset_1(esk3_0,esk5_0),esk5_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])).

cnf(c_0_129,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_130,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_114]),c_0_97])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,k8_relset_1(esk2_0,esk3_0,esk4_0,X1)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_115])).

cnf(c_0_132,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,k8_relset_1(esk2_0,esk3_0,esk4_0,X1))) = k8_relset_1(esk2_0,esk3_0,esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_115])).

cnf(c_0_133,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_37]),c_0_116]),c_0_116]),c_0_117])])).

cnf(c_0_134,negated_conjecture,
    ( k10_relat_1(esk4_0,k2_xboole_0(X1,esk3_0)) = k2_xboole_0(esk2_0,k10_relat_1(esk4_0,X1))
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120])).

cnf(c_0_135,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_136,plain,
    ( k3_subset_1(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_65]),c_0_123])])).

cnf(c_0_137,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(esk4_0,k3_subset_1(esk3_0,esk5_0)),k10_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126])])).

cnf(c_0_138,negated_conjecture,
    ( k2_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_111]),c_0_128]),c_0_120])).

cnf(c_0_139,negated_conjecture,
    ( k3_subset_1(esk2_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)) != k8_relset_1(esk2_0,esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_140,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_subset_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_129])).

cnf(c_0_141,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_subset_1(X1))) = k1_subset_1(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_129])).

cnf(c_0_142,plain,
    ( X1 = X2
    | ~ r1_xboole_0(k3_subset_1(X2,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_114]),c_0_130]),c_0_130]),c_0_117])])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,k10_relat_1(esk4_0,X1)),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_131,c_0_100])).

cnf(c_0_144,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,k10_relat_1(esk4_0,X1))) = k10_relat_1(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_100]),c_0_100])).

cnf(c_0_145,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_65])).

cnf(c_0_146,negated_conjecture,
    ( k2_xboole_0(esk2_0,k10_relat_1(esk4_0,esk3_0)) = k10_relat_1(esk4_0,esk3_0)
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_147,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_148,negated_conjecture,
    ( k3_subset_1(k10_relat_1(esk4_0,esk3_0),k10_relat_1(esk4_0,esk5_0)) = k10_relat_1(esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_118]),c_0_120]),c_0_138])).

cnf(c_0_149,negated_conjecture,
    ( k10_relat_1(esk4_0,k3_subset_1(esk3_0,esk5_0)) != k3_subset_1(esk2_0,k10_relat_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_100]),c_0_100])).

cnf(c_0_150,plain,
    ( X1 = k1_subset_1(X2)
    | ~ r1_xboole_0(k3_subset_1(X2,X1),k1_subset_1(X2))
    | ~ r1_xboole_0(X1,k3_subset_1(X2,k1_subset_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_140]),c_0_141]),c_0_141])).

cnf(c_0_151,plain,
    ( k1_subset_1(X1) = X1
    | ~ r1_xboole_0(k3_subset_1(X1,k1_subset_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_129])).

cnf(c_0_152,negated_conjecture,
    ( X1 = k10_relat_1(esk4_0,X2)
    | ~ r1_xboole_0(k3_subset_1(esk2_0,X1),k10_relat_1(esk4_0,X2))
    | ~ r1_xboole_0(X1,k3_subset_1(esk2_0,k10_relat_1(esk4_0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_143]),c_0_144]),c_0_144])).

cnf(c_0_153,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_xboole_0(esk2_0,k10_relat_1(esk4_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_147])).

cnf(c_0_154,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_119]),c_0_149])).

cnf(c_0_155,negated_conjecture,
    ( k1_subset_1(esk3_0) = esk5_0
    | ~ r1_xboole_0(k3_subset_1(esk3_0,esk5_0),k1_subset_1(esk3_0))
    | ~ r1_xboole_0(esk5_0,k3_subset_1(esk3_0,k1_subset_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_150,c_0_71])).

cnf(c_0_156,plain,
    ( k1_subset_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_151,c_0_117])).

cnf(c_0_157,negated_conjecture,
    ( k10_relat_1(esk4_0,X1) = esk2_0
    | ~ r1_xboole_0(esk2_0,k3_subset_1(esk2_0,k10_relat_1(esk4_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_37]),c_0_116]),c_0_45])])).

cnf(c_0_158,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_154]),c_0_126]),c_0_117])])).

cnf(c_0_159,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_155,c_0_154]),c_0_156]),c_0_154]),c_0_154]),c_0_156]),c_0_117]),c_0_154]),c_0_154]),c_0_156]),c_0_130]),c_0_117])])).

cnf(c_0_160,negated_conjecture,
    ( k10_relat_1(esk4_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_158]),c_0_158]),c_0_158]),c_0_45])])).

cnf(c_0_161,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_154]),c_0_159]),c_0_130]),c_0_160]),c_0_158]),c_0_159]),c_0_160]),c_0_130])]),
    [proof]).

%------------------------------------------------------------------------------
