%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t120_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:05 EDT 2019

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   81 (1108 expanded)
%              Number of clauses        :   56 ( 354 expanded)
%              Number of leaves         :   12 ( 275 expanded)
%              Depth                    :   13
%              Number of atoms          :  434 (9359 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t120_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tsep_1(X2,X3)
               => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X3,k8_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',t120_tmap_1)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',dt_k9_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',dt_k2_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',dt_k8_tmap_1)).

fof(fc5_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( ~ v2_struct_0(k8_tmap_1(X1,X2))
        & v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',fc5_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',d4_tmap_1)).

fof(t118_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',t118_tmap_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',dt_k2_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',t49_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t120_tmap_1.p',cc1_pre_topc)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_tsep_1(X2,X3)
                 => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3))
                    & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))
                    & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X3,k8_tmap_1(X1,X2))
                    & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t120_tmap_1])).

fof(c_0_13,plain,(
    ! [X29,X30] :
      ( ( v1_funct_1(k9_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X29) )
      & ( v1_funct_2(k9_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X29) )
      & ( m1_subset_1(k9_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & r1_tsep_1(esk2_0,esk3_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k8_tmap_1(esk1_0,esk2_0))
      | ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24] :
      ( ( v1_funct_1(k2_tmap_1(X21,X22,X23,X24))
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_struct_0(X24) )
      & ( v1_funct_2(k2_tmap_1(X21,X22,X23,X24),u1_struct_0(X24),u1_struct_0(X22))
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_struct_0(X24) )
      & ( m1_subset_1(k2_tmap_1(X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_struct_0(X24) ) ) ),
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
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_26,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( v2_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( l1_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_27,plain,(
    ! [X79,X80] :
      ( ( ~ v2_struct_0(k8_tmap_1(X79,X80))
        | v2_struct_0(X79)
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79)
        | ~ m1_pre_topc(X80,X79) )
      & ( v1_pre_topc(k8_tmap_1(X79,X80))
        | v2_struct_0(X79)
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79)
        | ~ m1_pre_topc(X80,X79) )
      & ( v2_pre_topc(k8_tmap_1(X79,X80))
        | v2_struct_0(X79)
        | ~ v2_pre_topc(X79)
        | ~ l1_pre_topc(X79)
        | ~ m1_pre_topc(X80,X79) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).

cnf(c_0_28,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_30,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k9_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_33,plain,(
    ! [X11,X12,X13,X14] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
      | ~ m1_pre_topc(X14,X11)
      | k2_tmap_1(X11,X12,X13,X14) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),X13,u1_struct_0(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_34,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X51,X52,X53,X54] :
      ( v2_struct_0(X51)
      | ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | v2_struct_0(X52)
      | ~ m1_pre_topc(X52,X51)
      | v2_struct_0(X53)
      | ~ m1_pre_topc(X53,X51)
      | ~ r1_tsep_1(X52,X53)
      | ~ m1_subset_1(X54,u1_struct_0(X53))
      | r1_tmap_1(X53,k8_tmap_1(X51,X52),k2_tmap_1(X51,k8_tmap_1(X51,X52),k9_tmap_1(X51,X52),X53),X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t118_tmap_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_29]),c_0_25])])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_29]),c_0_25])])).

fof(c_0_42,plain,(
    ! [X17,X18,X19,X20] :
      ( ( v1_funct_1(k2_partfun1(X17,X18,X19,X20))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(k2_partfun1(X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_51,plain,(
    ! [X61,X62,X63,X64] :
      ( ( ~ v5_pre_topc(X63,X62,X61)
        | ~ m1_subset_1(X64,u1_struct_0(X62))
        | r1_tmap_1(X62,X61,X63,X64)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,u1_struct_0(X62),u1_struct_0(X61))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X61))))
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( m1_subset_1(esk8_3(X61,X62,X63),u1_struct_0(X62))
        | v5_pre_topc(X63,X62,X61)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,u1_struct_0(X62),u1_struct_0(X61))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X61))))
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( ~ r1_tmap_1(X62,X61,X63,esk8_3(X61,X62,X63))
        | v5_pre_topc(X63,X62,X61)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,u1_struct_0(X62),u1_struct_0(X61))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X61))))
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | v2_struct_0(X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_18])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_struct_0(k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_18])])).

fof(c_0_55,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | l1_pre_topc(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_56,plain,(
    ! [X77,X78] :
      ( ~ v2_pre_topc(X77)
      | ~ l1_pre_topc(X77)
      | ~ m1_pre_topc(X78,X77)
      | v2_pre_topc(X78) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_57,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)),k9_tmap_1(esk1_0,esk2_0),u1_struct_0(X1)) = k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_29]),c_0_25]),c_0_44]),c_0_18]),c_0_45]),c_0_19])]),c_0_46]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk3_0,k8_tmap_1(X1,esk2_0),k2_tmap_1(X1,k8_tmap_1(X1,esk2_0),k9_tmap_1(X1,esk2_0),esk3_0),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X2))
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
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_39]),c_0_44])])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_39]),c_0_44])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_44])])).

cnf(c_0_65,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)),k9_tmap_1(esk1_0,esk2_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_29]),c_0_25])])).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)),k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk8_3(k8_tmap_1(esk1_0,esk2_0),X1,k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1)),u1_struct_0(X1))
    | v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1),X1,k8_tmap_1(esk1_0,esk2_0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_44]),c_0_45])]),c_0_46]),c_0_63]),c_0_64]),c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_59]),c_0_18])])).

cnf(c_0_72,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_18]),c_0_19])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k8_tmap_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk8_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_76,negated_conjecture,
    ( r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),esk8_3(k8_tmap_1(esk1_0,esk2_0),esk3_0,k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0)))
    | v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])]),c_0_49])).

cnf(c_0_77,negated_conjecture,
    ( ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),esk3_0,k8_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_78,negated_conjecture,
    ( ~ m1_subset_1(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_74]),c_0_44]),c_0_71]),c_0_45]),c_0_72])]),c_0_46]),c_0_49]),c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_62]),c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_39]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
