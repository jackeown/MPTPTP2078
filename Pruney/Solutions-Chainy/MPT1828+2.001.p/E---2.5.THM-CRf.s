%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:35 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   86 (5099 expanded)
%              Number of clauses        :   67 (1487 expanded)
%              Number of leaves         :    8 (1240 expanded)
%              Depth                    :   12
%              Number of atoms          :  919 (95659 expanded)
%              Number of equality atoms :   21 (  80 expanded)
%              Maximal formula depth    :   36 (   9 average)
%              Maximal clause size      :  134 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t144_tmap_1,conjecture,(
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
                 => ( ~ r1_tsep_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))
                                & r4_tsep_1(X1,X3,X4) )
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_tmap_1)).

fof(dt_k10_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1)
        & ~ v2_struct_0(X4)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
        & v1_funct_1(X6)
        & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
     => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
        & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(d13_tmap_1,axiom,(
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
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                         => ( ( r1_tsep_1(X3,X4)
                              | r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6)) )
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                               => ( X7 = k10_tmap_1(X1,X2,X3,X4,X5,X6)
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X7),X5)
                                    & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X7),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

fof(c_0_7,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( ~ r1_tsep_1(X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(X5,X3,X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                                & v5_pre_topc(X6,X4,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))
                                  & r4_tsep_1(X1,X3,X4) )
                               => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                  & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                  & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                  & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t144_tmap_1])).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k10_tmap_1(X19,X20,X21,X22,X23,X24))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))) )
      & ( v1_funct_2(k10_tmap_1(X19,X20,X21,X22,X23,X24),u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))) )
      & ( m1_subset_1(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ r1_tsep_1(esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))
    & r4_tsep_1(esk1_0,esk3_0,esk4_0)
    & ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
      | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
      | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_struct_0(k1_tsep_1(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) )
      & ( v1_pre_topc(k1_tsep_1(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) )
      & ( m1_pre_topc(k1_tsep_1(X25,X26,X27),X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_28,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( v1_funct_1(k3_tmap_1(X28,X29,X30,X31,X32))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X28)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29)))) )
      & ( v1_funct_2(k3_tmap_1(X28,X29,X30,X31,X32),u1_struct_0(X31),u1_struct_0(X29))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X28)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29)))) )
      & ( m1_subset_1(k3_tmap_1(X28,X29,X30,X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X28)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_29,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_37,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r1_tsep_1(X14,X15)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r1_tsep_1(X14,X15)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | ~ r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 = k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r1_tsep_1(X14,X15)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | ~ r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 = k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_tmap_1])])])])])).

fof(c_0_39,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r2_funct_2(X8,X9,X10,X11)
        | X10 = X11
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X10 != X11
        | r2_funct_2(X8,X9,X10,X11)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_32])]),c_0_16]),c_0_34])).

cnf(c_0_45,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | X5 != k10_tmap_1(X3,X2,X4,X1,X7,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X4,X1)),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X4,X1),X7),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X4,X1),X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | X5 != k10_tmap_1(X3,X2,X1,X4,X6,X7)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X1,X4)),u1_struct_0(X2),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X1,X4),X6),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X1,X4),X7))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_12]),c_0_13]),c_0_42]),c_0_43])]),c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_24])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X4),X4,k10_tmap_1(X2,X3,X1,X4,X5,X6)),X6)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X1,X4)),u1_struct_0(X3),k3_tmap_1(X2,X3,X1,k2_tsep_1(X2,X1,X4),X5),k3_tmap_1(X2,X3,X4,k2_tsep_1(X2,X1,X4),X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X3))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_19]),c_0_18]),c_0_10])).

cnf(c_0_51,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_53,plain,(
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

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X1),X4,k10_tmap_1(X2,X3,X4,X1,X5,X6)),X5)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X4,X1)),u1_struct_0(X3),k3_tmap_1(X2,X3,X4,k2_tsep_1(X2,X4,X1),X5),k3_tmap_1(X2,X3,X1,k2_tsep_1(X2,X4,X1),X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X3))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_19]),c_0_18]),c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_11]),c_0_14]),c_0_15])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_31]),c_0_30]),c_0_32]),c_0_12]),c_0_33]),c_0_13]),c_0_21]),c_0_11]),c_0_22]),c_0_14]),c_0_23]),c_0_15])]),c_0_16]),c_0_17]),c_0_34]),c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_12]),c_0_13]),c_0_42]),c_0_43])]),c_0_17])).

cnf(c_0_59,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_60,axiom,(
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
    inference(apply_def,[status(thm)],[t126_tmap_1,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_62,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_63,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_30]),c_0_31]),c_0_32]),c_0_12]),c_0_33]),c_0_13]),c_0_11]),c_0_21]),c_0_14]),c_0_22]),c_0_15]),c_0_23])]),c_0_24]),c_0_17]),c_0_34]),c_0_16])).

fof(c_0_64,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_30])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_41]),c_0_12]),c_0_13]),c_0_42]),c_0_43])]),c_0_17])).

fof(c_0_68,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ m1_pre_topc(X35,X33)
      | v2_struct_0(X36)
      | ~ m1_pre_topc(X36,X33)
      | ~ r4_tsep_1(X33,X35,X36)
      | ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,u1_struct_0(k1_tsep_1(X33,X35,X36)),u1_struct_0(X34))
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X33,X35,X36)),u1_struct_0(X34))))
      | epred1_5(X34,X35,X36,X37,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_60])])])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_43])])).

cnf(c_0_70,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_56]),c_0_63]),c_0_31])])).

fof(c_0_71,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ( v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_1(X45)
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))
        | ~ v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)
        | ~ m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_64])])])).

cnf(c_0_72,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_30])])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_49]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_76,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_42])])).

cnf(c_0_77,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_66]),c_0_31])])).

cnf(c_0_78,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_30])])).

cnf(c_0_80,negated_conjecture,
    ( epred1_5(esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_41]),c_0_75]),c_0_30]),c_0_31]),c_0_12]),c_0_32]),c_0_13]),c_0_33]),c_0_42]),c_0_43])]),c_0_16]),c_0_24]),c_0_17]),c_0_34])).

cnf(c_0_81,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_82,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_41])])).

cnf(c_0_83,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_73]),c_0_31])])).

cnf(c_0_84,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_85,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81]),c_0_11]),c_0_14]),c_0_15])]),c_0_82]),c_0_83]),c_0_84]),c_0_83]),c_0_21]),c_0_83]),c_0_22]),c_0_83]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 3.60/3.77  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 3.60/3.77  # and selection function SelectComplexExceptUniqMaxHorn.
% 3.60/3.77  #
% 3.60/3.77  # Preprocessing time       : 0.032 s
% 3.60/3.77  # Presaturation interreduction done
% 3.60/3.77  
% 3.60/3.77  # Proof found!
% 3.60/3.77  # SZS status Theorem
% 3.60/3.77  # SZS output start CNFRefutation
% 3.60/3.77  fof(t144_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X3,X4))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))&r4_tsep_1(X1,X3,X4))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_tmap_1)).
% 3.60/3.77  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 3.60/3.77  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 3.60/3.77  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 3.60/3.77  fof(d13_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((r1_tsep_1(X3,X4)|r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6)))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>(X7=k10_tmap_1(X1,X2,X3,X4,X5,X6)<=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X7),X5)&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X7),X6))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_tmap_1)).
% 3.60/3.77  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.60/3.77  fof(t126_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 3.60/3.77  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X3,X4))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))&r4_tsep_1(X1,X3,X4))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))))))))))), inference(assume_negation,[status(cth)],[t144_tmap_1])).
% 3.60/3.77  fof(c_0_8, plain, ![X19, X20, X21, X22, X23, X24]:(((v1_funct_1(k10_tmap_1(X19,X20,X21,X22,X23,X24))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)|v2_struct_0(X22)|~m1_pre_topc(X22,X19)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))))&(v1_funct_2(k10_tmap_1(X19,X20,X21,X22,X23,X24),u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)|v2_struct_0(X22)|~m1_pre_topc(X22,X19)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))))))&(m1_subset_1(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)|v2_struct_0(X22)|~m1_pre_topc(X22,X19)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 3.60/3.77  fof(c_0_9, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(~r1_tsep_1(esk3_0,esk4_0)&((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))&r4_tsep_1(esk1_0,esk3_0,esk4_0))&(~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 3.60/3.77  cnf(c_0_10, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.60/3.77  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_18, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.60/3.77  cnf(c_0_19, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.60/3.77  cnf(c_0_20, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 3.60/3.77  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_25, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 3.60/3.77  cnf(c_0_26, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 3.60/3.77  fof(c_0_27, plain, ![X25, X26, X27]:(((~v2_struct_0(k1_tsep_1(X25,X26,X27))|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25)))&(v1_pre_topc(k1_tsep_1(X25,X26,X27))|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25))))&(m1_pre_topc(k1_tsep_1(X25,X26,X27),X25)|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 3.60/3.77  fof(c_0_28, plain, ![X28, X29, X30, X31, X32]:(((v1_funct_1(k3_tmap_1(X28,X29,X30,X31,X32))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_pre_topc(X30,X28)|~m1_pre_topc(X31,X28)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))))&(v1_funct_2(k3_tmap_1(X28,X29,X30,X31,X32),u1_struct_0(X31),u1_struct_0(X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_pre_topc(X30,X28)|~m1_pre_topc(X31,X28)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29)))))))&(m1_subset_1(k3_tmap_1(X28,X29,X30,X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_pre_topc(X30,X28)|~m1_pre_topc(X31,X28)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 3.60/3.77  cnf(c_0_29, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 3.60/3.77  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_35, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 3.60/3.77  cnf(c_0_36, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 3.60/3.77  cnf(c_0_37, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.60/3.77  fof(c_0_38, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r1_tsep_1(X14,X15)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r1_tsep_1(X14,X15)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(~r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|~r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r1_tsep_1(X14,X15)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(((r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(~r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|~r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_tmap_1])])])])])).
% 3.60/3.77  fof(c_0_39, plain, ![X8, X9, X10, X11]:((~r2_funct_2(X8,X9,X10,X11)|X10=X11|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))&(X10!=X11|r2_funct_2(X8,X9,X10,X11)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 3.60/3.77  cnf(c_0_40, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.60/3.77  cnf(c_0_41, negated_conjecture, (m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 3.60/3.77  cnf(c_0_42, negated_conjecture, (v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 3.60/3.77  cnf(c_0_43, negated_conjecture, (v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_30]), c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 3.60/3.77  cnf(c_0_44, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_32])]), c_0_16]), c_0_34])).
% 3.60/3.77  cnf(c_0_45, plain, (r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|X5!=k10_tmap_1(X3,X2,X4,X1,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X3,X4,X1)),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X4,X1),X7),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X4,X1),X6))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_1(X7)|~v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.60/3.77  cnf(c_0_46, plain, (r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|X5!=k10_tmap_1(X3,X2,X1,X4,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X3,X1,X4)),u1_struct_0(X2),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X1,X4),X6),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X1,X4),X7))|~v1_funct_1(X7)|~v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.60/3.77  cnf(c_0_47, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.60/3.77  cnf(c_0_48, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_12]), c_0_13]), c_0_42]), c_0_43])]), c_0_17])).
% 3.60/3.77  cnf(c_0_49, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_24])).
% 3.60/3.77  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X4),X4,k10_tmap_1(X2,X3,X1,X4,X5,X6)),X6)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~r2_funct_2(u1_struct_0(k2_tsep_1(X2,X1,X4)),u1_struct_0(X3),k3_tmap_1(X2,X3,X1,k2_tsep_1(X2,X1,X4),X5),k3_tmap_1(X2,X3,X4,k2_tsep_1(X2,X1,X4),X6))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X3))|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X3))|~v1_funct_1(X5)|~v1_funct_1(X6)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_19]), c_0_18]), c_0_10])).
% 3.60/3.77  cnf(c_0_51, negated_conjecture, (r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_52, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.60/3.77  fof(c_0_53, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)<=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), introduced(definition)).
% 3.60/3.77  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X4),u1_struct_0(X3),k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X1),X4,k10_tmap_1(X2,X3,X4,X1,X5,X6)),X5)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~r2_funct_2(u1_struct_0(k2_tsep_1(X2,X4,X1)),u1_struct_0(X3),k3_tmap_1(X2,X3,X4,k2_tsep_1(X2,X4,X1),X5),k3_tmap_1(X2,X3,X1,k2_tsep_1(X2,X4,X1),X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))|~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X3))|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X3))|~v1_funct_1(X6)|~v1_funct_1(X5)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_19]), c_0_18]), c_0_10])).
% 3.60/3.77  cnf(c_0_55, negated_conjecture, (X1=esk6_0|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_11]), c_0_14]), c_0_15])])).
% 3.60/3.77  cnf(c_0_56, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_32]), c_0_33])]), c_0_34])).
% 3.60/3.77  cnf(c_0_57, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_31]), c_0_30]), c_0_32]), c_0_12]), c_0_33]), c_0_13]), c_0_21]), c_0_11]), c_0_22]), c_0_14]), c_0_23]), c_0_15])]), c_0_16]), c_0_17]), c_0_34]), c_0_24])).
% 3.60/3.77  cnf(c_0_58, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_12]), c_0_13]), c_0_42]), c_0_43])]), c_0_17])).
% 3.60/3.77  cnf(c_0_59, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.60/3.77  fof(c_0_60, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>epred1_5(X2,X3,X4,X5,X1))))))), inference(apply_def,[status(thm)],[t126_tmap_1, c_0_53])).
% 3.60/3.77  cnf(c_0_61, negated_conjecture, (~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_62, negated_conjecture, (X1=esk5_0|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_21]), c_0_22]), c_0_23])])).
% 3.60/3.77  cnf(c_0_63, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_30]), c_0_31]), c_0_32]), c_0_12]), c_0_33]), c_0_13]), c_0_11]), c_0_21]), c_0_14]), c_0_22]), c_0_15]), c_0_23])]), c_0_24]), c_0_17]), c_0_34]), c_0_16])).
% 3.60/3.77  fof(c_0_64, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), inference(split_equiv,[status(thm)],[c_0_53])).
% 3.60/3.77  cnf(c_0_65, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_30])])).
% 3.60/3.77  cnf(c_0_66, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_32]), c_0_33])]), c_0_34])).
% 3.60/3.77  cnf(c_0_67, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))|~m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_41]), c_0_12]), c_0_13]), c_0_42]), c_0_43])]), c_0_17])).
% 3.60/3.77  fof(c_0_68, plain, ![X33, X34, X35, X36, X37]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~m1_pre_topc(X35,X33)|(v2_struct_0(X36)|~m1_pre_topc(X36,X33)|(~r4_tsep_1(X33,X35,X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(k1_tsep_1(X33,X35,X36)),u1_struct_0(X34))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X33,X35,X36)),u1_struct_0(X34))))|epred1_5(X34,X35,X36,X37,X33))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_60])])])])).
% 3.60/3.77  cnf(c_0_69, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_43])])).
% 3.60/3.77  cnf(c_0_70, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk5_0|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_56]), c_0_63]), c_0_31])])).
% 3.60/3.77  fof(c_0_71, plain, ![X44, X45, X46, X47, X48]:(((((((((v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44))&(v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&((((v1_funct_1(X45)|(~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44))&(v1_funct_2(X45,u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|(~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v5_pre_topc(X45,k1_tsep_1(X44,X47,X46),X48)|(~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))|(~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),X47,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X47,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45))|~v1_funct_2(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),X46,X48)|~m1_subset_1(k3_tmap_1(X44,X48,k1_tsep_1(X44,X47,X46),X46,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_64])])])).
% 3.60/3.77  cnf(c_0_72, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_30])])).
% 3.60/3.77  cnf(c_0_73, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_49]), c_0_32]), c_0_33])]), c_0_34])).
% 3.60/3.77  cnf(c_0_74, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_5(X2,X3,X4,X5,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 3.60/3.77  cnf(c_0_75, negated_conjecture, (r4_tsep_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_76, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_42])])).
% 3.60/3.77  cnf(c_0_77, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk5_0|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_66]), c_0_31])])).
% 3.60/3.77  cnf(c_0_78, plain, (v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))|~epred1_5(X5,X3,X4,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 3.60/3.77  cnf(c_0_79, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_30])])).
% 3.60/3.77  cnf(c_0_80, negated_conjecture, (epred1_5(esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_41]), c_0_75]), c_0_30]), c_0_31]), c_0_12]), c_0_32]), c_0_13]), c_0_33]), c_0_42]), c_0_43])]), c_0_16]), c_0_24]), c_0_17]), c_0_34])).
% 3.60/3.77  cnf(c_0_81, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_82, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_41])])).
% 3.60/3.77  cnf(c_0_83, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_73]), c_0_31])])).
% 3.60/3.77  cnf(c_0_84, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.60/3.77  cnf(c_0_85, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81]), c_0_11]), c_0_14]), c_0_15])]), c_0_82]), c_0_83]), c_0_84]), c_0_83]), c_0_21]), c_0_83]), c_0_22]), c_0_83]), c_0_23])]), ['proof']).
% 3.60/3.77  # SZS output end CNFRefutation
% 3.60/3.77  # Proof object total steps             : 86
% 3.60/3.77  # Proof object clause steps            : 67
% 3.60/3.77  # Proof object formula steps           : 19
% 3.60/3.77  # Proof object conjectures             : 55
% 3.60/3.77  # Proof object clause conjectures      : 52
% 3.60/3.77  # Proof object formula conjectures     : 3
% 3.60/3.77  # Proof object initial clauses used    : 33
% 3.60/3.77  # Proof object initial formulas used   : 7
% 3.60/3.77  # Proof object generating inferences   : 29
% 3.60/3.77  # Proof object simplifying inferences  : 181
% 3.60/3.77  # Training examples: 0 positive, 0 negative
% 3.60/3.77  # Parsed axioms                        : 7
% 3.60/3.77  # Removed by relevancy pruning/SinE    : 0
% 3.60/3.77  # Initial clauses                      : 52
% 3.60/3.77  # Removed in clause preprocessing      : 0
% 3.60/3.77  # Initial clauses in saturation        : 52
% 3.60/3.77  # Processed clauses                    : 2945
% 3.60/3.77  # ...of these trivial                  : 2
% 3.60/3.77  # ...subsumed                          : 20
% 3.60/3.77  # ...remaining for further processing  : 2922
% 3.60/3.77  # Other redundant clauses eliminated   : 5
% 3.60/3.77  # Clauses deleted for lack of memory   : 0
% 3.60/3.77  # Backward-subsumed                    : 2
% 3.60/3.77  # Backward-rewritten                   : 7
% 3.60/3.77  # Generated clauses                    : 241066
% 3.60/3.77  # ...of the previous two non-trivial   : 241010
% 3.60/3.77  # Contextual simplify-reflections      : 122
% 3.60/3.77  # Paramodulations                      : 241061
% 3.60/3.77  # Factorizations                       : 0
% 3.60/3.77  # Equation resolutions                 : 5
% 3.60/3.77  # Propositional unsat checks           : 0
% 3.60/3.77  #    Propositional check models        : 0
% 3.60/3.77  #    Propositional check unsatisfiable : 0
% 3.60/3.77  #    Propositional clauses             : 0
% 3.60/3.77  #    Propositional clauses after purity: 0
% 3.60/3.77  #    Propositional unsat core size     : 0
% 3.60/3.77  #    Propositional preprocessing time  : 0.000
% 3.60/3.77  #    Propositional encoding time       : 0.000
% 3.60/3.77  #    Propositional solver time         : 0.000
% 3.60/3.77  #    Success case prop preproc time    : 0.000
% 3.60/3.77  #    Success case prop encoding time   : 0.000
% 3.60/3.77  #    Success case prop solver time     : 0.000
% 3.60/3.77  # Current number of processed clauses  : 2856
% 3.60/3.77  #    Positive orientable unit clauses  : 121
% 3.60/3.77  #    Positive unorientable unit clauses: 0
% 3.60/3.77  #    Negative unit clauses             : 6
% 3.60/3.77  #    Non-unit-clauses                  : 2729
% 3.60/3.77  # Current number of unprocessed clauses: 238169
% 3.60/3.77  # ...number of literals in the above   : 1537009
% 3.60/3.77  # Current number of archived formulas  : 0
% 3.60/3.77  # Current number of archived clauses   : 61
% 3.60/3.77  # Clause-clause subsumption calls (NU) : 2422491
% 3.60/3.77  # Rec. Clause-clause subsumption calls : 127706
% 3.60/3.77  # Non-unit clause-clause subsumptions  : 136
% 3.60/3.77  # Unit Clause-clause subsumption calls : 71209
% 3.60/3.77  # Rewrite failures with RHS unbound    : 0
% 3.60/3.77  # BW rewrite match attempts            : 7971
% 3.60/3.77  # BW rewrite match successes           : 5
% 3.60/3.77  # Condensation attempts                : 0
% 3.60/3.77  # Condensation successes               : 0
% 3.60/3.77  # Termbank termtop insertions          : 15847259
% 3.60/3.79  
% 3.60/3.79  # -------------------------------------------------
% 3.60/3.79  # User time                : 3.280 s
% 3.60/3.79  # System time              : 0.151 s
% 3.60/3.79  # Total time               : 3.432 s
% 3.60/3.79  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
