%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t177_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:37 EDT 2019

% Result     : Theorem 210.74s
% Output     : CNFRefutation 210.74s
% Verified   : 
% Statistics : Number of formulae       :  205 (1649 expanded)
%              Number of clauses        :  131 ( 722 expanded)
%              Number of leaves         :   37 ( 409 expanded)
%              Depth                    :   18
%              Number of atoms          :  392 (4705 expanded)
%              Number of equality atoms :  153 (1864 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',dt_k3_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',dt_k1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',existence_m1_subset_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t37_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t4_boole)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',redefinition_k9_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t3_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',dt_k9_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',involutiveness_k3_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t6_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',d5_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t3_boole)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t177_funct_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',d4_subset_1)).

fof(t48_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t48_funct_2)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',redefinition_k8_relset_1)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',dt_k8_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',cc1_relset_1)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t53_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t1_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',commutativity_k3_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t2_boole)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t175_relat_1)).

fof(t25_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t25_subset_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t79_xboole_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t8_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',dt_o_0_0_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',idempotence_k2_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',d7_xboole_0)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',redefinition_k4_subset_1)).

fof(t46_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ( r1_xboole_0(X2,X3)
              & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t46_subset_1)).

fof(t137_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t137_funct_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',commutativity_k2_xboole_0)).

fof(t171_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t177_funct_2.p',t171_relat_1)).

fof(c_0_37,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | m1_subset_1(k3_subset_1(X28,X29),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_38,plain,(
    ! [X26] : m1_subset_1(k1_subset_1(X26),k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_39,plain,(
    ! [X97,X98,X99] :
      ( ~ r2_hidden(X97,X98)
      | ~ m1_subset_1(X98,k1_zfmisc_1(X99))
      | ~ v1_xboole_0(X99) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_42,plain,(
    ! [X77,X78] :
      ( ~ m1_subset_1(X77,X78)
      | v1_xboole_0(X78)
      | r2_hidden(X77,X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_43,plain,(
    ! [X40] : m1_subset_1(esk5_1(X40),X40) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_44,plain,(
    ! [X79,X80] :
      ( ( k4_xboole_0(X79,X80) != k1_xboole_0
        | r1_tarski(X79,X80) )
      & ( ~ r1_tarski(X79,X80)
        | k4_xboole_0(X79,X80) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_45,plain,(
    ! [X90] : k4_xboole_0(k1_xboole_0,X90) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_46,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(X59))
      | k9_subset_1(X59,X60,X61) = k3_xboole_0(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_subset_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X82,X83] :
      ( ( ~ m1_subset_1(X82,k1_zfmisc_1(X83))
        | r1_tarski(X82,X83) )
      & ( ~ r1_tarski(X82,X83)
        | m1_subset_1(X82,k1_zfmisc_1(X83)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_54,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | m1_subset_1(k9_subset_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_55,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_56,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | k3_subset_1(X50,k3_subset_1(X50,X51)) = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_57,plain,(
    ! [X100] :
      ( ~ v1_xboole_0(X100)
      | X100 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_58,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_subset_1(X1,k1_subset_1(X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_60,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_63,plain,(
    ! [X81] : k4_xboole_0(X81,k1_xboole_0) = X81 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_64,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k9_subset_1(X1,X2,k1_subset_1(X1)) = k3_xboole_0(X2,k1_subset_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_41])).

cnf(c_0_66,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k3_subset_1(X1,k1_subset_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( m1_subset_1(k3_xboole_0(X1,k1_subset_1(X2)),k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_41]),c_0_65])).

cnf(c_0_73,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_subset_1(X1))) = k1_subset_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_41])).

cnf(c_0_74,plain,
    ( k3_subset_1(X1,k1_subset_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

fof(c_0_76,negated_conjecture,(
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

cnf(c_0_77,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_xboole_0(X3,k1_subset_1(X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_72])).

cnf(c_0_78,plain,
    ( k1_subset_1(X1) = X1
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

fof(c_0_79,plain,(
    ! [X27] : m1_subset_1(k2_subset_1(X27),k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_80,plain,(
    ! [X21] : k2_subset_1(X21) = X21 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_81,plain,(
    ! [X87,X88,X89] :
      ( ( X88 = k1_xboole_0
        | k8_relset_1(X87,X88,X89,X88) = X87
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X87,X88)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X87,X88))) )
      & ( X87 != k1_xboole_0
        | k8_relset_1(X87,X88,X89,X88) = X87
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X87,X88)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X87,X88))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).

fof(c_0_82,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & k3_subset_1(esk1_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk4_0)) != k8_relset_1(esk1_0,esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).

fof(c_0_83,plain,(
    ! [X55,X56,X57,X58] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | k8_relset_1(X55,X56,X57,X58) = k10_relat_1(X57,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_84,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | m1_subset_1(k8_relset_1(X33,X34,X35,X36),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

cnf(c_0_85,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,X1) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_93,plain,(
    ! [X107,X108,X109] :
      ( ~ m1_subset_1(X109,k1_zfmisc_1(k2_zfmisc_1(X107,X108)))
      | v1_relat_1(X109) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_95,plain,(
    ! [X94,X95,X96] : k4_xboole_0(X94,k2_xboole_0(X95,X96)) = k3_xboole_0(k4_xboole_0(X94,X95),k4_xboole_0(X94,X96)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

fof(c_0_96,plain,(
    ! [X71] : k2_xboole_0(X71,k1_xboole_0) = X71 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_97,plain,(
    ! [X13,X14] : k3_xboole_0(X13,X14) = k3_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_98,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_59])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_100,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

fof(c_0_101,plain,(
    ! [X76] : k3_xboole_0(X76,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_102,plain,(
    ! [X68,X69,X70] :
      ( ~ v1_relat_1(X70)
      | k10_relat_1(X70,k2_xboole_0(X68,X69)) = k2_xboole_0(k10_relat_1(X70,X68),k10_relat_1(X70,X69)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_103,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_91])])).

cnf(c_0_104,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_89])).

cnf(c_0_105,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_106,plain,(
    ! [X74,X75] :
      ( ~ m1_subset_1(X75,k1_zfmisc_1(X74))
      | k4_subset_1(X74,X75,k3_subset_1(X74,X75)) = k2_subset_1(X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k8_relset_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_89])).

fof(c_0_108,plain,(
    ! [X101,X102] : r1_xboole_0(k4_xboole_0(X101,X102),X102) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_110,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_111,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_113,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_98])).

cnf(c_0_114,plain,
    ( m1_subset_1(k3_subset_1(X1,esk5_1(k1_zfmisc_1(X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_50])).

fof(c_0_115,plain,(
    ! [X105,X106] :
      ( ~ v1_xboole_0(X105)
      | X105 = X106
      | ~ v1_xboole_0(X106) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_116,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_117,plain,
    ( r1_tarski(esk5_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_50])).

cnf(c_0_118,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_120,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_121,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_122,negated_conjecture,
    ( k10_relat_1(esk3_0,esk2_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_123,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_89])).

fof(c_0_124,plain,(
    ! [X42] : k2_xboole_0(X42,X42) = X42 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_125,plain,(
    ! [X24,X25] :
      ( ( ~ r1_xboole_0(X24,X25)
        | k3_xboole_0(X24,X25) = k1_xboole_0 )
      & ( k3_xboole_0(X24,X25) != k1_xboole_0
        | r1_xboole_0(X24,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_126,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(X52))
      | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
      | k4_subset_1(X52,X53,X54) = k2_xboole_0(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_127,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

fof(c_0_128,plain,(
    ! [X84,X85,X86] :
      ( ~ m1_subset_1(X85,k1_zfmisc_1(X84))
      | ~ m1_subset_1(X86,k1_zfmisc_1(X84))
      | ~ r1_xboole_0(X85,X86)
      | ~ r1_xboole_0(k3_subset_1(X84,X85),k3_subset_1(X84,X86))
      | X85 = k3_subset_1(X84,X86) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_subset_1])])])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X1)),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_107])).

cnf(c_0_130,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X1))) = k8_relset_1(esk1_0,esk2_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_107])).

fof(c_0_131,plain,(
    ! [X64,X65,X66] :
      ( ~ v1_relat_1(X66)
      | ~ v1_funct_1(X66)
      | k10_relat_1(X66,k3_xboole_0(X64,X65)) = k3_xboole_0(k10_relat_1(X66,X64),k10_relat_1(X66,X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).

cnf(c_0_132,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_133,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_109])).

cnf(c_0_134,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_71]),c_0_111]),c_0_112])).

cnf(c_0_135,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_136,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_subset_1(X1,esk5_1(k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_114])).

cnf(c_0_137,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_138,plain,
    ( k4_xboole_0(esk5_1(k1_zfmisc_1(X1)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_139,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_118])).

cnf(c_0_140,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_119])).

cnf(c_0_141,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_120,c_0_112])).

cnf(c_0_142,negated_conjecture,
    ( k10_relat_1(esk3_0,k2_xboole_0(esk2_0,X1)) = k2_xboole_0(esk1_0,k10_relat_1(esk3_0,X1))
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123])])).

cnf(c_0_143,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_144,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_145,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_146,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_127,c_0_87])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_109])).

cnf(c_0_148,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_109])).

fof(c_0_149,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k2_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_150,plain,
    ( X1 = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(k3_subset_1(X2,X1),k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,k10_relat_1(esk3_0,X1)),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_129,c_0_104])).

cnf(c_0_152,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,k10_relat_1(esk3_0,X1))) = k10_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_104]),c_0_104])).

cnf(c_0_153,plain,
    ( k10_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_154,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_155,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

fof(c_0_156,plain,(
    ! [X67] :
      ( ~ v1_relat_1(X67)
      | k10_relat_1(X67,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_relat_1])])).

cnf(c_0_157,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_158,plain,
    ( ~ v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k3_subset_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_159,plain,
    ( esk5_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_138])).

cnf(c_0_160,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_139])).

cnf(c_0_161,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_140]),c_0_141])).

cnf(c_0_162,negated_conjecture,
    ( k2_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)) = k10_relat_1(esk3_0,esk2_0)
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(k10_relat_1(esk3_0,X1),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_107,c_0_104])).

cnf(c_0_164,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_144,c_0_110])).

cnf(c_0_165,negated_conjecture,
    ( k4_subset_1(esk2_0,X1,esk4_0) = k2_xboole_0(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_109])).

cnf(c_0_166,negated_conjecture,
    ( k4_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0),esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_148])).

cnf(c_0_167,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_149])).

cnf(c_0_168,negated_conjecture,
    ( X1 = k10_relat_1(esk3_0,X2)
    | ~ r1_xboole_0(k3_subset_1(esk1_0,X1),k10_relat_1(esk3_0,X2))
    | ~ r1_xboole_0(X1,k3_subset_1(esk1_0,k10_relat_1(esk3_0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_152]),c_0_152])).

cnf(c_0_169,plain,
    ( r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | k10_relat_1(X1,k3_xboole_0(X2,X3)) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_144,c_0_153])).

cnf(c_0_170,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_112])).

cnf(c_0_171,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_156])).

cnf(c_0_172,negated_conjecture,
    ( k3_subset_1(esk1_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk4_0)) != k8_relset_1(esk1_0,esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_173,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_157])).

cnf(c_0_174,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_subset_1(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_159]),c_0_160])])).

cnf(c_0_175,negated_conjecture,
    ( k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_176,negated_conjecture,
    ( k4_xboole_0(esk1_0,k10_relat_1(esk3_0,X1)) = k3_subset_1(esk1_0,k10_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_163])).

cnf(c_0_177,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k10_relat_1(X2,X3)),k4_xboole_0(X1,k10_relat_1(X2,X4)))
    | k4_xboole_0(X1,k10_relat_1(X2,k2_xboole_0(X3,X4))) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_164,c_0_121])).

cnf(c_0_178,negated_conjecture,
    ( k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_147]),c_0_166]),c_0_167])).

cnf(c_0_179,negated_conjecture,
    ( k3_subset_1(esk1_0,k10_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,X2)
    | ~ r1_xboole_0(k3_subset_1(esk1_0,k10_relat_1(esk3_0,X1)),k3_subset_1(esk1_0,k10_relat_1(esk3_0,X2)))
    | ~ r1_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_151]),c_0_152])).

cnf(c_0_180,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(X1,esk4_0),k10_relat_1(X1,k3_subset_1(esk2_0,esk4_0)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_171])).

cnf(c_0_181,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_subset_1(esk2_0,esk4_0)) != k3_subset_1(esk1_0,k10_relat_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_172,c_0_104]),c_0_104])).

cnf(c_0_182,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_71])).

cnf(c_0_183,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_173])).

cnf(c_0_184,plain,
    ( v1_xboole_0(k3_subset_1(k1_xboole_0,X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_174,c_0_59])).

cnf(c_0_185,negated_conjecture,
    ( k3_subset_1(esk1_0,X1) = k10_relat_1(esk3_0,X2)
    | ~ v1_xboole_0(k3_subset_1(esk1_0,k10_relat_1(esk3_0,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_152,c_0_137])).

cnf(c_0_186,negated_conjecture,
    ( k3_subset_1(esk1_0,k10_relat_1(esk3_0,esk2_0)) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_175,c_0_176])).

cnf(c_0_187,plain,
    ( r1_tarski(k1_subset_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_41])).

cnf(c_0_188,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k10_relat_1(X2,esk4_0)),k4_xboole_0(X1,k10_relat_1(X2,k3_subset_1(esk2_0,esk4_0))))
    | k4_xboole_0(X1,k10_relat_1(X2,esk2_0)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_177,c_0_178])).

cnf(c_0_189,negated_conjecture,
    ( ~ r1_xboole_0(k3_subset_1(esk1_0,k10_relat_1(esk3_0,esk4_0)),k3_subset_1(esk1_0,k10_relat_1(esk3_0,k3_subset_1(esk2_0,esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_123]),c_0_91])]),c_0_181])).

cnf(c_0_190,plain,
    ( X1 = X2
    | ~ r1_xboole_0(k3_subset_1(X2,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_70]),c_0_182])]),c_0_75]),c_0_75])).

cnf(c_0_191,plain,
    ( m1_subset_1(k3_subset_1(k1_xboole_0,X1),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_183,c_0_184])).

cnf(c_0_192,negated_conjecture,
    ( k3_subset_1(esk1_0,X1) = k10_relat_1(esk3_0,esk2_0)
    | esk2_0 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_186]),c_0_160])])).

cnf(c_0_193,plain,
    ( k4_xboole_0(k1_subset_1(X1),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_187])).

cnf(c_0_194,negated_conjecture,
    ( k3_subset_1(esk1_0,k10_relat_1(esk3_0,esk2_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_176]),c_0_176]),c_0_176]),c_0_123])]),c_0_189])).

cnf(c_0_195,plain,
    ( k3_subset_1(k1_xboole_0,X1) = X2
    | ~ v1_xboole_0(X1)
    | ~ r1_xboole_0(k3_subset_1(X2,k3_subset_1(k1_xboole_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_190,c_0_191])).

cnf(c_0_196,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(X1,k1_subset_1(X1))) = k10_relat_1(esk3_0,esk2_0)
    | esk2_0 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_192,c_0_68])).

cnf(c_0_197,plain,
    ( k1_subset_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_193])).

cnf(c_0_198,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_199,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_186,c_0_194])).

cnf(c_0_200,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_171,c_0_123])).

cnf(c_0_201,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r1_xboole_0(k10_relat_1(esk3_0,esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_196]),c_0_197]),c_0_75]),c_0_197]),c_0_160]),c_0_160])]),c_0_198])).

cnf(c_0_202,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_132,c_0_53])).

cnf(c_0_203,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_194,c_0_199]),c_0_200]),c_0_75])).

cnf(c_0_204,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_201,c_0_199]),c_0_200]),c_0_202])]),c_0_203]),
    [proof]).
%------------------------------------------------------------------------------
