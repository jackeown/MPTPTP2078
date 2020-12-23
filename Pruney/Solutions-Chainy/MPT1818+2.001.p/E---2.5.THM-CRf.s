%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:34 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   96 (4248 expanded)
%              Number of clauses        :   79 (1257 expanded)
%              Number of leaves         :    7 (1035 expanded)
%              Depth                    :   15
%              Number of atoms          :  684 (141104 expanded)
%              Number of equality atoms :   18 (2977 expanded)
%              Maximal formula depth    :   50 (   7 average)
%              Maximal clause size      :   92 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t126_tmap_1,axiom,(
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
                          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                       => ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                            & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
                            & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
                            & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
                            & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
                            & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

fof(t134_tmap_1,conjecture,(
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
                    & v1_tsep_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & v1_tsep_1(X5,X1)
                        & m1_pre_topc(X5,X1) )
                     => ( X1 = k1_tsep_1(X1,X4,X5)
                       => ( ( v1_funct_1(X3)
                            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                            & v5_pre_topc(X3,X1,X2)
                            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_tmap_1)).

fof(t88_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tsep_1(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_tsep_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => r4_tsep_1(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(c_0_6,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
    <=> ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

fof(c_0_7,axiom,(
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
                          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                       => epred1_5(X2,X3,X4,X5,X1) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t126_tmap_1,c_0_6])).

fof(c_0_8,negated_conjecture,(
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
                      & v1_tsep_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & v1_tsep_1(X5,X1)
                          & m1_pre_topc(X5,X1) )
                       => ( X1 = k1_tsep_1(X1,X4,X5)
                         => ( ( v1_funct_1(X3)
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                              & v5_pre_topc(X3,X1,X2)
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                          <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                              & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                              & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                              & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                              & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                              & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                              & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_tmap_1])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X15)
      | v2_struct_0(X18)
      | ~ m1_pre_topc(X18,X15)
      | ~ r4_tsep_1(X15,X17,X18)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X17,X18)),u1_struct_0(X16))
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X17,X18)),u1_struct_0(X16))))
      | epred1_5(X16,X17,X18,X19,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,negated_conjecture,
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
    & v1_tsep_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & v1_tsep_1(esk5_0,esk1_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0)
    & ( ~ v1_funct_1(esk3_0)
      | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_1(esk3_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_1(esk3_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_1(esk3_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_1(esk3_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ v1_tsep_1(X22,X21)
      | ~ m1_pre_topc(X22,X21)
      | ~ v1_tsep_1(X23,X21)
      | ~ m1_pre_topc(X23,X21)
      | r4_tsep_1(X21,X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t88_tsep_1])])])])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X10)
      | ~ m1_pre_topc(X13,X10)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))
      | ~ m1_pre_topc(X13,X12)
      | k3_tmap_1(X10,X11,X12,X13,X14) = k2_partfun1(u1_struct_0(X12),u1_struct_0(X11),X14,u1_struct_0(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_13,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
     => ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_5(X2,X3,X4,X5,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | r4_tsep_1(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_tsep_1(X3,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_32,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | m1_pre_topc(X20,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_33,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33))))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v1_funct_1(X30)
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) )
      & ( m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | ~ v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))
        | ~ v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))
        | ~ v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)
        | ~ m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33))))
        | ~ epred1_5(X33,X32,X31,X30,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_34,negated_conjecture,
    ( epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(esk1_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( r4_tsep_1(esk1_0,X1,esk5_0)
    | ~ v1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_16]),c_0_18]),c_0_19])]),c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_37,plain,(
    ! [X6,X7,X8,X9] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ m1_pre_topc(X9,X6)
      | k2_tmap_1(X6,X7,X8,X9) = k2_partfun1(u1_struct_0(X6),u1_struct_0(X7),X8,u1_struct_0(X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_17])])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk5_0,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_18]),c_0_30]),c_0_19])]),c_0_31]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_16]),c_0_18]),c_0_19])]),c_0_22])).

cnf(c_0_49,plain,
    ( v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_1(esk3_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_27]),c_0_28])]),c_0_46])])).

cnf(c_0_54,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_16])])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),esk5_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_17]),c_0_18]),c_0_19])]),c_0_22])).

cnf(c_0_60,plain,
    ( v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_28]),c_0_27]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_46]),c_0_26]),c_0_27]),c_0_28])]),c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_26]),c_0_46]),c_0_27]),c_0_28])])).

cnf(c_0_65,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_59]),c_0_17])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_67,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),esk4_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_15])).

cnf(c_0_68,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_69,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])]),c_0_63])])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_65]),c_0_46]),c_0_26]),c_0_27]),c_0_28])]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_75,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_76,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])]),c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_26]),c_0_54]),c_0_46]),c_0_27]),c_0_28])]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_80,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_81,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_26]),c_0_65]),c_0_46]),c_0_27]),c_0_28])]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_15])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_85,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_86,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_54]),c_0_46]),c_0_26]),c_0_27]),c_0_28])]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_15])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_90,plain,
    ( v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
    | ~ epred1_5(X5,X3,X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_91,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_65]),c_0_46]),c_0_26]),c_0_27]),c_0_28])]),c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( v5_pre_topc(X1,esk1_0,X2)
    | ~ epred1_5(X2,esk4_0,esk5_0,X1,esk1_0)
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),esk5_0,X2)
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),esk4_0,X2)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_15])).

cnf(c_0_94,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_54]),c_0_46]),c_0_63]),c_0_65]),c_0_72]),c_0_87]),c_0_65]),c_0_92]),c_0_77]),c_0_65]),c_0_82]),c_0_62]),c_0_65]),c_0_71])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:59:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.030 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t126_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_tmap_1)).
% 0.18/0.38  fof(t134_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X1))&m1_pre_topc(X4,X1))=>![X5]:(((~(v2_struct_0(X5))&v1_tsep_1(X5,X1))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_tmap_1)).
% 0.18/0.38  fof(t88_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))=>![X3]:((v1_tsep_1(X3,X1)&m1_pre_topc(X3,X1))=>r4_tsep_1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tsep_1)).
% 0.18/0.38  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.18/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.18/0.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.38  fof(c_0_6, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)<=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), introduced(definition)).
% 0.18/0.38  fof(c_0_7, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>epred1_5(X2,X3,X4,X5,X1))))))), inference(apply_def,[status(thm)],[t126_tmap_1, c_0_6])).
% 0.18/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X1))&m1_pre_topc(X4,X1))=>![X5]:(((~(v2_struct_0(X5))&v1_tsep_1(X5,X1))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t134_tmap_1])).
% 0.18/0.38  fof(c_0_9, plain, ![X15, X16, X17, X18, X19]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15)|(v2_struct_0(X18)|~m1_pre_topc(X18,X15)|(~r4_tsep_1(X15,X17,X18)|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X17,X18)),u1_struct_0(X16))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X17,X18)),u1_struct_0(X16))))|epred1_5(X16,X17,X18,X19,X15))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.18/0.38  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((~v2_struct_0(esk4_0)&v1_tsep_1(esk4_0,esk1_0))&m1_pre_topc(esk4_0,esk1_0))&(((~v2_struct_0(esk5_0)&v1_tsep_1(esk5_0,esk1_0))&m1_pre_topc(esk5_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&((~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|(~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))))&(((((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_1(esk3_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_1(esk3_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.18/0.38  fof(c_0_11, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~v1_tsep_1(X22,X21)|~m1_pre_topc(X22,X21)|(~v1_tsep_1(X23,X21)|~m1_pre_topc(X23,X21)|r4_tsep_1(X21,X22,X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t88_tsep_1])])])])).
% 0.18/0.38  fof(c_0_12, plain, ![X10, X11, X12, X13, X14]:(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_pre_topc(X12,X10)|(~m1_pre_topc(X13,X10)|(~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))|(~m1_pre_topc(X13,X12)|k3_tmap_1(X10,X11,X12,X13,X14)=k2_partfun1(u1_struct_0(X12),u1_struct_0(X11),X14,u1_struct_0(X13)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.18/0.38  fof(c_0_13, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), inference(split_equiv,[status(thm)],[c_0_6])).
% 0.18/0.38  cnf(c_0_14, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_5(X2,X3,X4,X5,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.38  cnf(c_0_15, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_23, plain, (v2_struct_0(X1)|r4_tsep_1(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~v1_tsep_1(X3,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  cnf(c_0_24, negated_conjecture, (v1_tsep_1(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  fof(c_0_32, plain, ![X20]:(~l1_pre_topc(X20)|m1_pre_topc(X20,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.18/0.38  fof(c_0_33, plain, ![X29, X30, X31, X32, X33]:(((((((((v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29))&(v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33))))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|~v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&((((v1_funct_1(X30)|(~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29))&(v1_funct_2(X30,u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))|(~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(v5_pre_topc(X30,k1_tsep_1(X29,X32,X31),X33)|(~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))&(m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X32,X31)),u1_struct_0(X33))))|(~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),u1_struct_0(X32),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),X32,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X32,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|~v1_funct_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30))|~v1_funct_2(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),u1_struct_0(X31),u1_struct_0(X33))|~v5_pre_topc(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),X31,X33)|~m1_subset_1(k3_tmap_1(X29,X33,k1_tsep_1(X29,X32,X31),X31,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X33)))))|~epred1_5(X33,X32,X31,X30,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|v2_struct_0(X1)|~r4_tsep_1(esk1_0,esk4_0,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20]), c_0_21]), c_0_22])).
% 0.18/0.38  cnf(c_0_35, negated_conjecture, (r4_tsep_1(esk1_0,X1,esk5_0)|~v1_tsep_1(X1,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_16]), c_0_18]), c_0_19])]), c_0_22])).
% 0.18/0.38  cnf(c_0_36, negated_conjecture, (v1_tsep_1(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  fof(c_0_37, plain, ![X6, X7, X8, X9]:(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))|(~m1_pre_topc(X9,X6)|k2_tmap_1(X6,X7,X8,X9)=k2_partfun1(u1_struct_0(X6),u1_struct_0(X7),X8,u1_struct_0(X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.38  cnf(c_0_38, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.18/0.38  cnf(c_0_39, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.38  cnf(c_0_40, plain, (v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.38  cnf(c_0_41, negated_conjecture, (epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_17])])).
% 0.18/0.38  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.38  cnf(c_0_43, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk5_0,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_16])).
% 0.18/0.38  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_18])).
% 0.18/0.38  cnf(c_0_45, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_15])).
% 0.18/0.38  cnf(c_0_46, negated_conjecture, (epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.18/0.38  cnf(c_0_47, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_18]), c_0_30]), c_0_19])]), c_0_31]), c_0_22])).
% 0.18/0.38  cnf(c_0_48, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_16]), c_0_18]), c_0_19])]), c_0_22])).
% 0.18/0.38  cnf(c_0_49, plain, (v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_50, plain, (v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_51, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_17])).
% 0.18/0.39  cnf(c_0_52, negated_conjecture, (~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_53, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_27]), c_0_28])]), c_0_46])])).
% 0.18/0.39  cnf(c_0_54, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_16])])).
% 0.18/0.39  cnf(c_0_55, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_56, negated_conjecture, (v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),esk5_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_49, c_0_15])).
% 0.18/0.39  cnf(c_0_57, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_58, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_50, c_0_15])).
% 0.18/0.39  cnf(c_0_59, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_17]), c_0_18]), c_0_19])]), c_0_22])).
% 0.18/0.39  cnf(c_0_60, plain, (v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_61, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_28]), c_0_27]), c_0_26])])).
% 0.18/0.39  cnf(c_0_62, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.18/0.39  cnf(c_0_63, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_54]), c_0_46]), c_0_26]), c_0_27]), c_0_28])]), c_0_57])).
% 0.18/0.39  cnf(c_0_64, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_26]), c_0_46]), c_0_27]), c_0_28])])).
% 0.18/0.39  cnf(c_0_65, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_59]), c_0_17])])).
% 0.18/0.39  cnf(c_0_66, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_67, negated_conjecture, (v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),esk4_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_60, c_0_15])).
% 0.18/0.39  cnf(c_0_68, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_69, plain, (v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_70, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])]), c_0_63])])).
% 0.18/0.39  cnf(c_0_71, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.18/0.39  cnf(c_0_72, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_65]), c_0_46]), c_0_26]), c_0_27]), c_0_28])]), c_0_68])).
% 0.18/0.39  cnf(c_0_73, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_69, c_0_15])).
% 0.18/0.39  cnf(c_0_74, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_75, plain, (v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_76, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])]), c_0_72])])).
% 0.18/0.39  cnf(c_0_77, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_26]), c_0_54]), c_0_46]), c_0_27]), c_0_28])]), c_0_74])).
% 0.18/0.39  cnf(c_0_78, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),u1_struct_0(esk4_0),u1_struct_0(X1))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_75, c_0_15])).
% 0.18/0.39  cnf(c_0_79, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_80, plain, (m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_81, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.18/0.39  cnf(c_0_82, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_26]), c_0_65]), c_0_46]), c_0_27]), c_0_28])]), c_0_79])).
% 0.18/0.39  cnf(c_0_83, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_80, c_0_15])).
% 0.18/0.39  cnf(c_0_84, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_85, plain, (m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_86, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.18/0.39  cnf(c_0_87, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_54]), c_0_46]), c_0_26]), c_0_27]), c_0_28])]), c_0_84])).
% 0.18/0.39  cnf(c_0_88, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_85, c_0_15])).
% 0.18/0.39  cnf(c_0_89, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_90, plain, (v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))|~epred1_5(X5,X3,X4,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_91, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.18/0.39  cnf(c_0_92, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_65]), c_0_46]), c_0_26]), c_0_27]), c_0_28])]), c_0_89])).
% 0.18/0.39  cnf(c_0_93, negated_conjecture, (v5_pre_topc(X1,esk1_0,X2)|~epred1_5(X2,esk4_0,esk5_0,X1,esk1_0)|~v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),esk5_0,X2)|~v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),esk4_0,X2)|~m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))|~m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))|~v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1))|~v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1))), inference(spm,[status(thm)],[c_0_90, c_0_15])).
% 0.18/0.39  cnf(c_0_94, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.18/0.39  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_54]), c_0_46]), c_0_63]), c_0_65]), c_0_72]), c_0_87]), c_0_65]), c_0_92]), c_0_77]), c_0_65]), c_0_82]), c_0_62]), c_0_65]), c_0_71])]), c_0_94]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 96
% 0.18/0.39  # Proof object clause steps            : 79
% 0.18/0.39  # Proof object formula steps           : 17
% 0.18/0.39  # Proof object conjectures             : 68
% 0.18/0.39  # Proof object clause conjectures      : 65
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 39
% 0.18/0.39  # Proof object initial formulas used   : 6
% 0.18/0.39  # Proof object generating inferences   : 31
% 0.18/0.39  # Proof object simplifying inferences  : 135
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 6
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 66
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 66
% 0.18/0.39  # Processed clauses                    : 176
% 0.18/0.39  # ...of these trivial                  : 24
% 0.18/0.39  # ...subsumed                          : 1
% 0.18/0.39  # ...remaining for further processing  : 151
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 13
% 0.18/0.39  # Backward-rewritten                   : 14
% 0.18/0.39  # Generated clauses                    : 102
% 0.18/0.39  # ...of the previous two non-trivial   : 95
% 0.18/0.39  # Contextual simplify-reflections      : 36
% 0.18/0.39  # Paramodulations                      : 102
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 0
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 82
% 0.18/0.39  #    Positive orientable unit clauses  : 29
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 5
% 0.18/0.39  #    Non-unit-clauses                  : 48
% 0.18/0.39  # Current number of unprocessed clauses: 27
% 0.18/0.39  # ...number of literals in the above   : 335
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 69
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 2434
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 127
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 42
% 0.18/0.39  # Unit Clause-clause subsumption calls : 71
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 42
% 0.18/0.39  # BW rewrite match successes           : 14
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 14528
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.049 s
% 0.18/0.39  # System time              : 0.005 s
% 0.18/0.39  # Total time               : 0.054 s
% 0.18/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
