%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t97_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:24 EDT 2019

% Result     : Theorem 255.46s
% Output     : CNFRefutation 255.46s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 256 expanded)
%              Number of clauses        :   49 (  93 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 (1589 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',redefinition_r2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',dt_k6_partfun1)).

fof(t97_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X4,X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k4_tmap_1(X1,X3),X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',t97_tmap_1)).

fof(t23_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',t23_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',fc8_funct_2)).

fof(dt_k3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v1_funct_1(k3_struct_0(X1))
        & v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',dt_k3_struct_0)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',dt_k4_relset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',dt_l1_pre_topc)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',redefinition_k4_relset_1)).

fof(d4_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',d4_struct_0)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',redefinition_k1_partfun1)).

fof(t69_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X2),u1_struct_0(X3))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                         => r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X5,X6),X4),k1_partfun1(u1_struct_0(X4),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),k2_tmap_1(X1,X2,X5,X4),X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',t69_tmap_1)).

fof(d7_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',d7_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t97_tmap_1.p',fc2_struct_0)).

fof(c_0_14,plain,(
    ! [X75,X76,X77,X78] :
      ( ( ~ r2_relset_1(X75,X76,X77,X78)
        | X77 = X78
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) )
      & ( X77 != X78
        | r2_relset_1(X75,X76,X77,X78)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_15,plain,(
    ! [X41] :
      ( v1_partfun1(k6_partfun1(X41),X41)
      & m1_subset_1(k6_partfun1(X41),k1_zfmisc_1(k2_zfmisc_1(X41,X41))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                   => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X4,X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k4_tmap_1(X1,X3),X4)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t97_tmap_1])).

cnf(c_0_17,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X97,X98,X99] :
      ( ( r2_relset_1(X97,X98,k4_relset_1(X97,X97,X97,X98,k6_partfun1(X97),X99),X99)
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) )
      & ( r2_relset_1(X97,X98,k4_relset_1(X97,X98,X98,X98,X99,k6_partfun1(X98)),X99)
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X122,X123,X124,X125,X126] :
      ( ( v1_funct_1(k5_relat_1(X125,X126))
        | v1_xboole_0(X123)
        | ~ v1_funct_1(X125)
        | ~ v1_funct_2(X125,X122,X123)
        | ~ m1_subset_1(X125,k1_zfmisc_1(k2_zfmisc_1(X122,X123)))
        | ~ v1_funct_1(X126)
        | ~ v1_funct_2(X126,X123,X124)
        | ~ m1_subset_1(X126,k1_zfmisc_1(k2_zfmisc_1(X123,X124))) )
      & ( v1_funct_2(k5_relat_1(X125,X126),X122,X124)
        | v1_xboole_0(X123)
        | ~ v1_funct_1(X125)
        | ~ v1_funct_2(X125,X122,X123)
        | ~ m1_subset_1(X125,k1_zfmisc_1(k2_zfmisc_1(X122,X123)))
        | ~ v1_funct_1(X126)
        | ~ v1_funct_2(X126,X123,X124)
        | ~ m1_subset_1(X126,k1_zfmisc_1(k2_zfmisc_1(X123,X124))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).

fof(c_0_22,plain,(
    ! [X30] :
      ( ( v1_funct_1(k3_struct_0(X30))
        | ~ l1_struct_0(X30) )
      & ( v1_funct_2(k3_struct_0(X30),u1_struct_0(X30),u1_struct_0(X30))
        | ~ l1_struct_0(X30) )
      & ( m1_subset_1(k3_struct_0(X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X30))))
        | ~ l1_struct_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_struct_0])])])).

cnf(c_0_23,plain,
    ( X1 = k6_partfun1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | m1_subset_1(k4_relset_1(X31,X32,X33,X34,X35,X36),k1_zfmisc_1(k2_zfmisc_1(X31,X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_funct_1(k3_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X45] :
      ( ~ l1_pre_topc(X45)
      | l1_struct_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_32,plain,(
    ! [X64,X65,X66,X67,X68,X69] :
      ( ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
      | k4_relset_1(X64,X65,X66,X67,X68,X69) = k5_relat_1(X68,X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_33,plain,
    ( k4_relset_1(X1,X1,X1,X1,k6_partfun1(X1),k6_partfun1(X1)) = k6_partfun1(X1)
    | ~ m1_subset_1(k4_relset_1(X1,X1,X1,X1,k6_partfun1(X1),k6_partfun1(X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_26])).

cnf(c_0_36,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v1_funct_1(k5_relat_1(X2,k3_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(X1))))
    | ~ v1_funct_2(X2,X3,u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_relset_1(X1,X1,X1,X1,k6_partfun1(X1),k6_partfun1(X1)) = k6_partfun1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_18])])).

fof(c_0_41,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k3_struct_0(X13) = k6_partfun1(u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_struct_0])])).

fof(c_0_42,plain,(
    ! [X54,X55,X56,X57,X58,X59] :
      ( ~ v1_funct_1(X58)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | ~ v1_funct_1(X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | k1_partfun1(X54,X55,X56,X57,X58,X59) = k5_relat_1(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_43,negated_conjecture,
    ( k4_relset_1(u1_struct_0(esk1_0),X1,X2,u1_struct_0(esk2_0),X3,X4) = esk4_0
    | ~ r2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_relset_1(u1_struct_0(esk1_0),X1,X2,u1_struct_0(esk2_0),X3,X4),esk4_0)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_44,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v1_funct_1(k5_relat_1(k3_struct_0(X1),k3_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( k5_relat_1(k6_partfun1(X1),k6_partfun1(X1)) = k6_partfun1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18])])).

cnf(c_0_47,plain,
    ( k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X110,X111,X112,X113,X114,X115] :
      ( v2_struct_0(X110)
      | ~ v2_pre_topc(X110)
      | ~ l1_pre_topc(X110)
      | v2_struct_0(X111)
      | ~ v2_pre_topc(X111)
      | ~ l1_pre_topc(X111)
      | v2_struct_0(X112)
      | ~ v2_pre_topc(X112)
      | ~ l1_pre_topc(X112)
      | v2_struct_0(X113)
      | ~ m1_pre_topc(X113,X110)
      | ~ v1_funct_1(X114)
      | ~ v1_funct_2(X114,u1_struct_0(X110),u1_struct_0(X111))
      | ~ m1_subset_1(X114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X110),u1_struct_0(X111))))
      | ~ v1_funct_1(X115)
      | ~ v1_funct_2(X115,u1_struct_0(X111),u1_struct_0(X112))
      | ~ m1_subset_1(X115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X111),u1_struct_0(X112))))
      | r2_funct_2(u1_struct_0(X113),u1_struct_0(X112),k2_tmap_1(X110,X112,k1_partfun1(u1_struct_0(X110),u1_struct_0(X111),u1_struct_0(X111),u1_struct_0(X112),X114,X115),X113),k1_partfun1(u1_struct_0(X113),u1_struct_0(X111),u1_struct_0(X111),u1_struct_0(X112),k2_tmap_1(X110,X111,X114,X113),X115)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_tmap_1])])])])).

cnf(c_0_49,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_51,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | k4_tmap_1(X14,X15) = k2_tmap_1(X14,X14,k3_struct_0(X14),X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_tmap_1])])])])).

cnf(c_0_52,negated_conjecture,
    ( k4_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k6_partfun1(u1_struct_0(esk1_0)),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_26]),c_0_18])])).

fof(c_0_53,plain,(
    ! [X121] :
      ( v2_struct_0(X121)
      | ~ l1_struct_0(X121)
      | ~ v1_xboole_0(u1_struct_0(X121)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v1_funct_1(k5_relat_1(k3_struct_0(esk1_0),k3_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( k5_relat_1(k3_struct_0(X1),k3_struct_0(X1)) = k3_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X5,X6),X4),k1_partfun1(u1_struct_0(X4),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),k2_tmap_1(X1,X2,X5,X4),X6))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k1_partfun1(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_26]),c_0_50])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( k5_relat_1(k6_partfun1(u1_struct_0(esk1_0)),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_52]),c_0_26]),c_0_18])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v1_funct_1(k3_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_45])])).

cnf(c_0_69,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(X2,esk2_0,k5_relat_1(X3,esk4_0),X1),k1_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tmap_1(X2,esk1_0,X3,X1),esk4_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk1_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26]),c_0_58]),c_0_50]),c_0_59]),c_0_38]),c_0_60]),c_0_61])]),c_0_62]),c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk3_0) = k4_tmap_1(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_38]),c_0_61])]),c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k5_relat_1(k3_struct_0(esk1_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_47]),c_0_45])])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k3_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_45])]),c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),k4_tmap_1(esk1_0,esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_subset_1(k3_struct_0(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))
    | ~ v1_funct_2(k3_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72]),c_0_65]),c_0_38]),c_0_61])]),c_0_73]),c_0_63]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(k3_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_45])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_30]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
