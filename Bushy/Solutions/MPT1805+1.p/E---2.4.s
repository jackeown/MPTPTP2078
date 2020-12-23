%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t121_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:05 EDT 2019

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   76 (1094 expanded)
%              Number of clauses        :   51 ( 349 expanded)
%              Number of leaves         :   12 ( 272 expanded)
%              Depth                    :   12
%              Number of atoms          :  401 (7418 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t121_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
            & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
            & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
            & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',t121_tmap_1)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',dt_k9_tmap_1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',dt_k2_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',dt_k8_tmap_1)).

fof(fc5_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( ~ v2_struct_0(k8_tmap_1(X1,X2))
        & v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',fc5_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',dt_l1_pre_topc)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',d4_tmap_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',dt_k2_partfun1)).

fof(t119_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',t119_tmap_1)).

fof(t49_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',t49_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t121_tmap_1.p',cc1_pre_topc)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
              & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
              & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
              & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t121_tmap_1])).

fof(c_0_13,plain,(
    ! [X28,X29] :
      ( ( v1_funct_1(k9_tmap_1(X28,X29))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( v1_funct_2(k9_tmap_1(X28,X29),u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( m1_subset_1(k9_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),esk2_0,k8_tmap_1(esk1_0,esk2_0))
      | ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X20,X21,X22,X23] :
      ( ( v1_funct_1(k2_tmap_1(X20,X21,X22,X23))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_struct_0(X23) )
      & ( v1_funct_2(k2_tmap_1(X20,X21,X22,X23),u1_struct_0(X23),u1_struct_0(X21))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_struct_0(X23) )
      & ( m1_subset_1(k2_tmap_1(X20,X21,X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | ~ l1_struct_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_16,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X26,X27] :
      ( ( v1_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( v2_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( l1_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_24,plain,(
    ! [X75,X76] :
      ( ( ~ v2_struct_0(k8_tmap_1(X75,X76))
        | v2_struct_0(X75)
        | ~ v2_pre_topc(X75)
        | ~ l1_pre_topc(X75)
        | ~ m1_pre_topc(X76,X75) )
      & ( v1_pre_topc(k8_tmap_1(X75,X76))
        | v2_struct_0(X75)
        | ~ v2_pre_topc(X75)
        | ~ l1_pre_topc(X75)
        | ~ m1_pre_topc(X76,X75) )
      & ( v2_pre_topc(k8_tmap_1(X75,X76))
        | v2_struct_0(X75)
        | ~ v2_pre_topc(X75)
        | ~ l1_pre_topc(X75)
        | ~ m1_pre_topc(X76,X75) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).

cnf(c_0_25,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_29,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_30,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_32,plain,(
    ! [X10,X11,X12,X13] :
      ( v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
      | ~ m1_pre_topc(X13,X10)
      | k2_tmap_1(X10,X11,X12,X13) = k2_partfun1(u1_struct_0(X10),u1_struct_0(X11),X12,u1_struct_0(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_33,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_37,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_28])]),c_0_27])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_28])])).

fof(c_0_40,plain,(
    ! [X16,X17,X18,X19] :
      ( ( v1_funct_1(k2_partfun1(X16,X17,X18,X19))
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( m1_subset_1(k2_partfun1(X16,X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_45,plain,(
    ! [X48,X49,X50] :
      ( v2_struct_0(X48)
      | ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | v2_struct_0(X49)
      | ~ m1_pre_topc(X49,X48)
      | ~ m1_subset_1(X50,u1_struct_0(X49))
      | r1_tmap_1(X49,k8_tmap_1(X48,X49),k2_tmap_1(X48,k8_tmap_1(X48,X49),k9_tmap_1(X48,X49),X49),X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t119_tmap_1])])])])).

fof(c_0_46,plain,(
    ! [X57,X58,X59,X60] :
      ( ( ~ v5_pre_topc(X59,X58,X57)
        | ~ m1_subset_1(X60,u1_struct_0(X58))
        | r1_tmap_1(X58,X57,X59,X60)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,u1_struct_0(X58),u1_struct_0(X57))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X57))))
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | v2_struct_0(X57)
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) )
      & ( m1_subset_1(esk7_3(X57,X58,X59),u1_struct_0(X58))
        | v5_pre_topc(X59,X58,X57)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,u1_struct_0(X58),u1_struct_0(X57))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X57))))
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | v2_struct_0(X57)
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) )
      & ( ~ r1_tmap_1(X58,X57,X59,esk7_3(X57,X58,X59))
        | v5_pre_topc(X59,X58,X57)
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,u1_struct_0(X58),u1_struct_0(X57))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X57))))
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | v2_struct_0(X57)
        | ~ v2_pre_topc(X57)
        | ~ l1_pre_topc(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18])])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_18])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_18])])).

fof(c_0_50,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | l1_pre_topc(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_51,plain,(
    ! [X73,X74] :
      ( ~ v2_pre_topc(X73)
      | ~ l1_pre_topc(X73)
      | ~ m1_pre_topc(X74,X73)
      | v2_pre_topc(X74) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_52,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)),k9_tmap_1(esk1_0,esk2_0),u1_struct_0(X1)) = k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_27]),c_0_28]),c_0_42]),c_0_18]),c_0_43]),c_0_19])]),c_0_44]),c_0_20])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X2))
    | v5_pre_topc(X3,X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_42])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_37]),c_0_42])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_42])])).

cnf(c_0_60,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)),k9_tmap_1(esk1_0,esk2_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_27]),c_0_28])])).

cnf(c_0_63,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)),k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0)) = k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(esk2_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_17]),c_0_18]),c_0_19])]),c_0_55]),c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk7_3(k8_tmap_1(esk1_0,esk2_0),X1,k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1)),u1_struct_0(X1))
    | v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),X1,k8_tmap_1(esk1_0,esk2_0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_42]),c_0_43])]),c_0_44]),c_0_58]),c_0_59]),c_0_37])).

cnf(c_0_66,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_17]),c_0_18])])).

cnf(c_0_67,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),esk2_0,k8_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk7_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_71,negated_conjecture,
    ( r1_tmap_1(esk2_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),esk7_3(k8_tmap_1(esk1_0,esk2_0),esk2_0,k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0)))
    | v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),esk2_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67])]),c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),esk2_0,k8_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_69]),c_0_42]),c_0_66]),c_0_43]),c_0_67])]),c_0_44]),c_0_55]),c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_57]),c_0_59])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_37]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
