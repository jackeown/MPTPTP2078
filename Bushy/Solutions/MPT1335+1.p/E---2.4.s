%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t58_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:41 EDT 2019

% Result     : Theorem 152.37s
% Output     : CNFRefutation 152.37s
% Verified   : 
% Statistics : Number of formulae       :  110 (1070 expanded)
%              Number of clauses        :   77 ( 388 expanded)
%              Number of leaves         :   16 ( 259 expanded)
%              Depth                    :   19
%              Number of atoms          :  375 (8188 expanded)
%              Number of equality atoms :   23 ( 122 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t2_subset)).

fof(t58_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( ( v5_pre_topc(X4,X1,X3)
                          & v5_pre_topc(X5,X3,X2) )
                       => v5_pre_topc(k1_partfun1(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X2),X4,X5),X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t58_tops_2)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',dt_k8_relset_1)).

fof(fc8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v1_xboole_0(X2)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X2,X3)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k5_relat_1(X4,X5))
        & v1_funct_2(k5_relat_1(X4,X5),X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',fc8_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t6_boole)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',redefinition_k8_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',redefinition_k1_partfun1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t8_boole)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',dt_k1_partfun1)).

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',d12_pre_topc)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',cc1_relset_1)).

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t181_relat_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',dt_l1_pre_topc)).

fof(c_0_16,plain,(
    ! [X58,X59,X60] :
      ( ~ r2_hidden(X58,X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(X60))
      | ~ v1_xboole_0(X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X34] : m1_subset_1(esk9_1(X34),X34) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X51,X52)
      | v1_xboole_0(X52)
      | r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & l1_pre_topc(X3) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ( ( v5_pre_topc(X4,X1,X3)
                            & v5_pre_topc(X5,X3,X2) )
                         => v5_pre_topc(k1_partfun1(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X2),X4,X5),X1,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_tops_2])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk9_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k8_relset_1(X27,X28,X29,X30),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_25,plain,(
    ! [X70,X71,X72,X73,X74] :
      ( ( v1_funct_1(k5_relat_1(X73,X74))
        | v1_xboole_0(X71)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X70,X71)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,X71,X72)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X71,X72))) )
      & ( v1_funct_2(k5_relat_1(X73,X74),X70,X72)
        | v1_xboole_0(X71)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X70,X71)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | ~ v1_funct_1(X74)
        | ~ v1_funct_2(X74,X71,X72)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X71,X72))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).

fof(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v5_pre_topc(esk4_0,esk1_0,esk3_0)
    & v5_pre_topc(esk5_0,esk3_0,esk2_0)
    & ~ v5_pre_topc(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk5_0),esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_27,plain,(
    ! [X61] :
      ( ~ v1_xboole_0(X61)
      | X61 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(esk9_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,esk9_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k8_relset_1(X42,X43,X44,X45) = k10_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_31,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_xboole_0(esk9_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k8_relset_1(X1,X3,X4,X5))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_38,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_funct_1(k5_relat_1(X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( esk9_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k8_relset_1(X1,X2,X3,X4))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X5,k8_relset_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k10_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

fof(c_0_48,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ~ v1_funct_1(X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | ~ v1_funct_1(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k1_partfun1(X36,X37,X38,X39,X40,X41) = k5_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_49,plain,(
    ! [X64,X65] :
      ( ~ v1_xboole_0(X64)
      | X64 = X65
      | ~ v1_xboole_0(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(k10_relat_1(esk5_0,X1))
    | ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,k10_relat_1(esk5_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_45]),c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

fof(c_0_53,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k1_partfun1(X19,X20,X21,X22,X23,X24))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( m1_subset_1(k1_partfun1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X19,X22)))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_54,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(k10_relat_1(esk5_0,X1))
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(X2,k10_relat_1(esk5_0,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k1_partfun1(X1,X2,u1_struct_0(esk3_0),u1_struct_0(esk2_0),X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_34])])).

cnf(c_0_59,negated_conjecture,
    ( X1 = u1_struct_0(esk3_0)
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(k10_relat_1(esk5_0,X1))
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_32]),c_0_34])])).

cnf(c_0_62,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk5_0,X1) = u1_struct_0(esk3_0)
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_64,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v5_pre_topc(X16,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v4_pre_topc(X17,X15)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,X17),X14)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk6_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( v4_pre_topc(esk6_3(X14,X15,X16),X15)
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X14),u1_struct_0(X15),X16,esk6_3(X14,X15,X16)),X14)
        | v5_pre_topc(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_42])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_58]),c_0_32]),c_0_34])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),k10_relat_1(esk5_0,X1))))
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk5_0),esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_69,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),esk4_0,X1) = k10_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_71,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_74,plain,(
    ! [X66,X67,X68] :
      ( ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
      | v1_relat_1(X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_75,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk6_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k5_relat_1(esk4_0,esk5_0),X1) = k10_relat_1(k5_relat_1(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_42])])).

cnf(c_0_78,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_79,negated_conjecture,
    ( ~ v5_pre_topc(k5_relat_1(esk4_0,esk5_0),esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_58]),c_0_40]),c_0_42])])).

cnf(c_0_80,plain,
    ( v1_funct_2(k5_relat_1(X1,X2),X3,X4)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,X1),esk1_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_40]),c_0_41]),c_0_42]),c_0_72]),c_0_73])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k10_relat_1(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_45]),c_0_32])])).

fof(c_0_83,plain,(
    ! [X46,X47,X48] :
      ( ~ v1_relat_1(X47)
      | ~ v1_relat_1(X48)
      | k10_relat_1(k5_relat_1(X47,X48),X46) = k10_relat_1(X47,k10_relat_1(X48,X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

cnf(c_0_84,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_86,plain,
    ( v4_pre_topc(esk6_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_87,negated_conjecture,
    ( ~ v4_pre_topc(k10_relat_1(k5_relat_1(esk4_0,esk5_0),esk6_3(esk1_0,esk2_0,k5_relat_1(esk4_0,esk5_0))),esk1_0)
    | ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_65]),c_0_77]),c_0_78]),c_0_73])]),c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_funct_2(k5_relat_1(X1,esk5_0),X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_89,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,k10_relat_1(esk5_0,X1)),esk1_0)
    | ~ v4_pre_topc(k10_relat_1(esk5_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_32])).

cnf(c_0_92,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_40])).

cnf(c_0_93,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk2_0,k5_relat_1(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_65]),c_0_77]),c_0_78]),c_0_73])]),c_0_79])).

cnf(c_0_95,negated_conjecture,
    ( v4_pre_topc(esk6_3(esk1_0,esk2_0,k5_relat_1(esk4_0,esk5_0)),esk2_0)
    | ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_65]),c_0_77]),c_0_78]),c_0_73])]),c_0_79])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v4_pre_topc(k10_relat_1(k5_relat_1(esk4_0,esk5_0),esk6_3(esk1_0,esk2_0,k5_relat_1(esk4_0,esk5_0))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_97,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(k5_relat_1(esk4_0,esk5_0),X1),esk1_0)
    | ~ v4_pre_topc(k10_relat_1(esk5_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_92])])).

fof(c_0_98,plain,(
    ! [X69] :
      ( v2_struct_0(X69)
      | ~ l1_struct_0(X69)
      | ~ v1_xboole_0(u1_struct_0(X69)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_99,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk5_0,X1),esk3_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_45]),c_0_93]),c_0_32]),c_0_33]),c_0_34]),c_0_78]),c_0_72])])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk6_3(esk1_0,esk2_0,k5_relat_1(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_88]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v4_pre_topc(esk6_3(esk1_0,esk2_0,k5_relat_1(esk4_0,esk5_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_88]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v4_pre_topc(k10_relat_1(esk5_0,esk6_3(esk1_0,esk2_0,k5_relat_1(esk4_0,esk5_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101]),c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_106,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_107,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])).

cnf(c_0_108,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
