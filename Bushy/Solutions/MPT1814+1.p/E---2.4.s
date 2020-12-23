%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t130_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:06 EDT 2019

% Result     : Theorem 152.71s
% Output     : CNFRefutation 152.71s
% Verified   : 
% Statistics : Number of formulae       :  140 (7275 expanded)
%              Number of clauses        :  111 (2276 expanded)
%              Number of leaves         :   13 (1760 expanded)
%              Depth                    :   18
%              Number of atoms          :  860 (223155 expanded)
%              Number of equality atoms :   16 ( 541 expanded)
%              Maximal formula depth    :   49 (   6 average)
%              Maximal clause size      :   91 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t130_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & v1_borsuk_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & v1_borsuk_1(X5,X1)
                        & m1_pre_topc(X5,X1) )
                     => ( ( v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
                          & v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
                          & v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
                          & m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2)))) )
                      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                          & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                          & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                          & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                          & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                          & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',t130_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',redefinition_k2_partfun1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',dt_k1_tsep_1)).

fof(t129_tmap_1,axiom,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',t129_tmap_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',dt_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',d4_tmap_1)).

fof(t87_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_borsuk_1(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_borsuk_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => r4_tsep_1(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',t87_tsep_1)).

fof(symmetry_r4_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_pre_topc(X2,X1)
        & m1_pre_topc(X3,X1) )
     => ( r4_tsep_1(X1,X2,X3)
       => r4_tsep_1(X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',symmetry_r4_tsep_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',commutativity_k1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t130_tmap_1.p',dt_m1_pre_topc)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
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
                    ( ( ~ v2_struct_0(X4)
                      & v1_borsuk_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & v1_borsuk_1(X5,X1)
                          & m1_pre_topc(X5,X1) )
                       => ( ( v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t130_tmap_1])).

fof(c_0_13,plain,(
    ! [X5,X4,X3,X2,X1] :
      ( epred1_5(X1,X2,X4,X5,X3)
    <=> ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

fof(c_0_14,plain,(
    ! [X50,X51,X52,X53] :
      ( ~ v1_funct_1(X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | k2_partfun1(X50,X51,X52,X53) = k7_relat_1(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk4_0)
    & v1_borsuk_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & v1_borsuk_1(esk5_0,esk1_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_16,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v2_struct_0(k1_tsep_1(X23,X24,X25))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23) )
      & ( v1_pre_topc(k1_tsep_1(X23,X24,X25))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23) )
      & ( m1_pre_topc(k1_tsep_1(X23,X24,X25),X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_17,axiom,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => epred1_5(X1,X2,X4,X5,X3) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t129_tmap_1,c_0_13])).

fof(c_0_18,plain,(
    ! [X26,X27,X28,X29] :
      ( ( v1_funct_1(k2_partfun1(X26,X27,X28,X29))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( m1_subset_1(k2_partfun1(X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_19,plain,(
    ! [X17,X18,X19,X20] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
      | ~ m1_pre_topc(X20,X17)
      | k2_tmap_1(X17,X18,X19,X20) = k2_partfun1(u1_struct_0(X17),u1_struct_0(X18),X19,u1_struct_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_20,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X57,X58,X59,X60,X61] :
      ( v2_struct_0(X57)
      | ~ v2_pre_topc(X57)
      | ~ l1_pre_topc(X57)
      | v2_struct_0(X58)
      | ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | v2_struct_0(X59)
      | ~ m1_pre_topc(X59,X57)
      | v2_struct_0(X60)
      | ~ m1_pre_topc(X60,X57)
      | ~ r4_tsep_1(X57,X59,X60)
      | ~ v1_funct_1(X61)
      | ~ v1_funct_2(X61,u1_struct_0(X57),u1_struct_0(X58))
      | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X57),u1_struct_0(X58))))
      | epred1_5(X57,X58,X60,X61,X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_29,plain,(
    ! [X77,X78,X79] :
      ( v2_struct_0(X77)
      | ~ v2_pre_topc(X77)
      | ~ l1_pre_topc(X77)
      | ~ v1_borsuk_1(X78,X77)
      | ~ m1_pre_topc(X78,X77)
      | ~ v1_borsuk_1(X79,X77)
      | ~ m1_pre_topc(X79,X77)
      | r4_tsep_1(X77,X78,X79) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t87_tsep_1])])])])).

cnf(c_0_30,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_5(X1,X2,X4,X5,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r4_tsep_1(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_borsuk_1(X3,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( v1_borsuk_1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_44,plain,(
    ! [X5,X4,X3,X2,X1] :
      ( epred1_5(X1,X2,X4,X5,X3)
     => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_22])])).

cnf(c_0_46,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_21]),c_0_22]),c_0_33]),c_0_25]),c_0_34]),c_0_35])]),c_0_36]),c_0_27]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk4_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( epred1_5(esk1_0,esk2_0,X1,esk3_0,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(esk1_0,X2,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_21]),c_0_22]),c_0_33]),c_0_25]),c_0_34]),c_0_35])]),c_0_36]),c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( r4_tsep_1(esk1_0,X1,esk5_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ v1_borsuk_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_24]),c_0_43]),c_0_25]),c_0_35])]),c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_51,plain,(
    ! [X89,X90,X91,X92,X93] :
      ( ( v1_funct_1(k2_tmap_1(X93,X92,X89,X91))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v1_funct_2(k2_tmap_1(X93,X92,X89,X91),u1_struct_0(X91),u1_struct_0(X92))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v5_pre_topc(k2_tmap_1(X93,X92,X89,X91),X91,X92)
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( m1_subset_1(k2_tmap_1(X93,X92,X89,X91),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X91),u1_struct_0(X92))))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v1_funct_1(k2_tmap_1(X93,X92,X89,X90))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v1_funct_2(k2_tmap_1(X93,X92,X89,X90),u1_struct_0(X90),u1_struct_0(X92))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v5_pre_topc(k2_tmap_1(X93,X92,X89,X90),X90,X92)
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( m1_subset_1(k2_tmap_1(X93,X92,X89,X90),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X90),u1_struct_0(X92))))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v1_funct_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X91))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X91),u1_struct_0(X91),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X91),X91,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X91),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X91),u1_struct_0(X92))))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X90))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X90),u1_struct_0(X90),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X90),X90,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X90),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X90),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v1_funct_2(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X91))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X91),u1_struct_0(X91),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X91),X91,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X91),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X91),u1_struct_0(X92))))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X90))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X90),u1_struct_0(X90),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X90),X90,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X90),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X90),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( v5_pre_topc(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_tsep_1(X93,X91,X90),X92)
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X91))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X91),u1_struct_0(X91),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X91),X91,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X91),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X91),u1_struct_0(X92))))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X90))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X90),u1_struct_0(X90),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X90),X90,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X90),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X90),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) )
      & ( m1_subset_1(k2_tmap_1(X93,X92,X89,k1_tsep_1(X93,X91,X90)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X93,X91,X90)),u1_struct_0(X92))))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X91))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X91),u1_struct_0(X91),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X91),X91,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X91),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X91),u1_struct_0(X92))))
        | ~ v1_funct_1(k2_tmap_1(X93,X92,X89,X90))
        | ~ v1_funct_2(k2_tmap_1(X93,X92,X89,X90),u1_struct_0(X90),u1_struct_0(X92))
        | ~ v5_pre_topc(k2_tmap_1(X93,X92,X89,X90),X90,X92)
        | ~ m1_subset_1(k2_tmap_1(X93,X92,X89,X90),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X90),u1_struct_0(X92))))
        | ~ epred1_5(X93,X92,X90,X89,X91) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0))) = k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( epred1_5(esk1_0,esk2_0,esk5_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(esk1_0,X1,esk5_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_39]),c_0_50])])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_24])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X1,X2,X5,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X1,X2,X5,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( epred1_5(esk1_0,esk2_0,esk5_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_39]),c_0_56])]),c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_68,plain,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])]),c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_70,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X1,X2,X5,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_74,plain,(
    ! [X54,X55,X56] :
      ( ~ l1_pre_topc(X54)
      | ~ m1_pre_topc(X55,X54)
      | ~ m1_pre_topc(X56,X54)
      | ~ r4_tsep_1(X54,X55,X56)
      | r4_tsep_1(X54,X56,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r4_tsep_1])])).

fof(c_0_75,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | k1_tsep_1(X14,X15,X16) = k1_tsep_1(X14,X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

cnf(c_0_76,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X1,X2,X5,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_77,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])]),c_0_61]),c_0_59])])).

cnf(c_0_78,plain,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_79,plain,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_61]),c_0_62])]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_80,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X1,X2,X5,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_84,plain,
    ( r4_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ r4_tsep_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_tsep_1(esk1_0,X1,esk4_0),esk2_0)
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_59])).

cnf(c_0_87,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X1,X2,X5,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_88,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_69])])).

cnf(c_0_89,plain,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_61]),c_0_62])]),c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(esk1_0,X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_40])).

cnf(c_0_92,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_56]),c_0_24]),c_0_39]),c_0_25])])).

cnf(c_0_93,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk5_0) = k1_tsep_1(esk1_0,esk5_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_94,plain,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_tsep_1(esk1_0,X1,esk4_0),esk2_0)
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_69])])).

cnf(c_0_95,plain,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_59])).

cnf(c_0_96,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_79])])).

cnf(c_0_97,plain,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_98,negated_conjecture,
    ( epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_24]),c_0_92])]),c_0_26])).

cnf(c_0_99,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk5_0,esk4_0) = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_39]),c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_102,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_103,plain,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_tsep_1(esk1_0,X1,esk4_0),esk2_0)
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_79])])).

cnf(c_0_104,plain,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_69])])).

cnf(c_0_105,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_90])])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_99]),c_0_67])]),c_0_100]),c_0_101]),c_0_102])).

cnf(c_0_107,plain,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),k1_tsep_1(esk1_0,X1,esk4_0),esk2_0)
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_90])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_110,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_111,plain,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_79])])).

fof(c_0_112,plain,(
    ! [X30,X31,X32,X33] :
      ( ( v1_funct_1(k2_tmap_1(X30,X31,X32,X33))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ l1_struct_0(X33) )
      & ( v1_funct_2(k2_tmap_1(X30,X31,X32,X33),u1_struct_0(X33),u1_struct_0(X31))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ l1_struct_0(X33) )
      & ( m1_subset_1(k2_tmap_1(X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ l1_struct_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_113,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106])])).

cnf(c_0_114,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_98]),c_0_99]),c_0_99]),c_0_67])]),c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_115,plain,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(k1_tsep_1(esk1_0,X1,esk4_0)),u1_struct_0(esk2_0))
    | ~ epred1_5(esk1_0,esk2_0,esk4_0,esk3_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_90])])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_118,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_119,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

fof(c_0_120,plain,(
    ! [X36] :
      ( ~ l1_pre_topc(X36)
      | l1_struct_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_121,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_122,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])])).

cnf(c_0_123,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_98]),c_0_99]),c_0_99]),c_0_67])]),c_0_116]),c_0_117]),c_0_118])).

cnf(c_0_124,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X1,X2,X4,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_32]),c_0_21]),c_0_22])])).

cnf(c_0_126,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_32]),c_0_21]),c_0_22])])).

cnf(c_0_128,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123])])).

cnf(c_0_129,plain,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_61]),c_0_62]),c_0_114]),c_0_106]),c_0_123])])).

cnf(c_0_130,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_33])])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_126]),c_0_33])])).

fof(c_0_132,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | l1_pre_topc(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_133,negated_conjecture,
    ( ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_134,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_126]),c_0_25])])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_126]),c_0_25])])).

cnf(c_0_136,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_132])).

cnf(c_0_137,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_24]),c_0_25])])).

cnf(c_0_139,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_126]),c_0_138])]),
    [proof]).
%------------------------------------------------------------------------------
