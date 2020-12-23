%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1830+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:34 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  252 (4569 expanded)
%              Number of clauses        :  174 ( 898 expanded)
%              Number of leaves         :   15 (2046 expanded)
%              Depth                    :   22
%              Number of atoms          : 2498 (107917 expanded)
%              Number of equality atoms :  602 (1771 expanded)
%              Maximal formula depth    :   26 (  10 average)
%              Maximal clause size      :   52 (   9 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(X4,X2,X1)
                            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(X5,X3,X1)
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),sK7))
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK7,X3,X1)
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(X5,X3,X1)
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(X4,X2,X1)
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_tsep_1(X0,X2,X3),X1)
              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5)) )
            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),sK6),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK6,X2,X1)
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & ~ r1_tsep_1(X2,X3)
          & m1_pre_topc(X3,X0)
          & v1_borsuk_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,sK5),X4),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,X2,sK5),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK5,X1)
                & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & ~ r1_tsep_1(X2,sK5)
        & m1_pre_topc(sK5,X0)
        & v1_borsuk_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & ~ r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,X0)
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,sK4,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & ~ r1_tsep_1(sK4,X3)
            & m1_pre_topc(X3,X0)
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & v1_borsuk_1(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),sK3)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,sK3,X3,k2_tsep_1(X0,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(X5,X3,sK3)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & ~ r1_tsep_1(X2,X3)
                & m1_pre_topc(X3,X0)
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_borsuk_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & ~ r1_tsep_1(X2,X3)
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,sK2)
                  & v1_borsuk_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & v1_borsuk_1(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & ~ r1_tsep_1(sK4,sK5)
    & m1_pre_topc(sK5,sK2)
    & v1_borsuk_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & v1_borsuk_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f41,f40,f39,f38,f37,f36])).

fof(f92,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f32])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f25,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f29])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f25,f24])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_borsuk_1(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_29,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_453,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1308,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_25,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | r1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_457,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_55,X1_55)),X1_55)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_55),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_55))
    | ~ v1_funct_2(X1_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X0_55,u1_struct_0(X3_54),u1_struct_0(X1_54))
    | r1_tsep_1(X3_54,X0_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1304,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_55,X1_55)),X1_55) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_55),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_55)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | r1_tsep_1(X3_54,X0_54) = iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_7783,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1304])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_51,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_52,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_53,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_54,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_55,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_56,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_57,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_42,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_59,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_60,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_62,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_63,plain,
    ( r1_tsep_1(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_64,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_65,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_67,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_68,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_69,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_71,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_72,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2184,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,k1_tsep_1(sK2,sK4,X0_54),X0_54,k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_55,X1_55)),X1_55)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,sK4,k2_tsep_1(sK2,sK4,X0_54),X0_55),k3_tmap_1(sK2,X1_54,X0_54,k2_tsep_1(sK2,sK4,X0_54),X1_55))
    | ~ v1_funct_2(X1_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_54))
    | r1_tsep_1(sK4,X0_54)
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_2919,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X0_54),X0_54,k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_55)),X0_55)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X0_54)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X0_54),sK6),k3_tmap_1(sK2,sK3,X0_54,k2_tsep_1(sK2,sK4,X0_54),X0_55))
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | r1_tsep_1(sK4,X0_54)
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2184])).

cnf(c_3433,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | r1_tsep_1(sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2919])).

cnf(c_3434,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3433])).

cnf(c_7786,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7783,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_63,c_64,c_65,c_67,c_68,c_69,c_71,c_72,c_3434])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1284,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_452,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1309,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_9,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_473,plain,
    ( ~ r2_funct_2(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X1_55,X0_56,X1_56)
    | ~ v1_funct_2(X0_55,X0_56,X1_56)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | X1_55 = X0_55 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1288,plain,
    ( X0_55 = X1_55
    | r2_funct_2(X0_56,X1_56,X1_55,X0_55) != iProver_top
    | v1_funct_2(X1_55,X0_56,X1_56) != iProver_top
    | v1_funct_2(X0_55,X0_56,X1_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_5113,plain,
    ( sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1288])).

cnf(c_6252,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5113,c_68,c_69])).

cnf(c_6253,plain,
    ( sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_6252])).

cnf(c_6939,plain,
    ( k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55),sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_6253])).

cnf(c_8899,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55),sK7) != iProver_top
    | k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55) = sK7
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6939,c_54,c_55,c_56])).

cnf(c_8900,plain,
    ( k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55),sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,sK3,X1_54,sK5,X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8899])).

cnf(c_8917,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7786,c_8900])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_479,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(k1_tsep_1(X1_54,X2_54,X0_54),X1_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2044,plain,
    ( ~ m1_pre_topc(X0_54,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,sK4,X0_54),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_2288,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_481,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_55,X0_55),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2149,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_54))
    | v1_funct_2(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2368,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X0_54))
    | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_55,X0_55),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_2851,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_2853,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2851])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_482,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2159,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_54))))
    | m1_subset_1(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_55,X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_2388,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X1_55) ),
    inference(instantiation,[status(thm)],[c_2159])).

cnf(c_2901,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2388])).

cnf(c_2903,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2901])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_476,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_55),u1_struct_0(X3_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2080,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(sK2,X1_54,X0_54,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_2649,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_55),u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2080])).

cnf(c_4225,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_2649])).

cnf(c_4227,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_4225])).

cnf(c_448,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1313,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1281,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_55,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_3788,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_55,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1281])).

cnf(c_4558,plain,
    ( v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_55,sK7)) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3788,c_54,c_55,c_56,c_60,c_68,c_69])).

cnf(c_4559,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_55,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4558])).

cnf(c_4575,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_4559])).

cnf(c_4729,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,X0_54)
    | ~ m1_pre_topc(sK4,X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4575])).

cnf(c_4731,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_4729])).

cnf(c_8918,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8917])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_475,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_55)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2619,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(X1_54,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),X1_54,X0_55)) ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_4364,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0_54,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_2619])).

cnf(c_8993,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_4364])).

cnf(c_8995,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_8993])).

cnf(c_9058,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8917,c_50,c_49,c_48,c_47,c_46,c_45,c_44,c_42,c_41,c_39,c_37,c_36,c_34,c_33,c_32,c_30,c_2288,c_2853,c_2903,c_4227,c_4731,c_8918,c_8995])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_467,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),X1_54,X0_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),X2_54,X0_54)
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),u1_struct_0(X2_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55))
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1294,plain,
    ( sP0(X0_54,X1_54,X0_55,X2_54,X3_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),X1_54,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),X2_54,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_9065,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9058,c_1294])).

cnf(c_9085,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9065,c_9058])).

cnf(c_31,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_70,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2289,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2288])).

cnf(c_2852,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2851])).

cnf(c_2854,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2852])).

cnf(c_2902,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2901])).

cnf(c_2904,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2902])).

cnf(c_2085,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(sK2,X1_54,X0_54,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_2648,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_55),u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_4220,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_2648])).

cnf(c_4221,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4220])).

cnf(c_4223,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4221])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_471,plain,
    ( ~ sP1(X0_54,X1_54,X0_55,X2_54,X3_54)
    | ~ sP0(X3_54,X2_54,X0_55,X1_54,X0_54)
    | v5_pre_topc(X0_55,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1290,plain,
    ( sP1(X0_54,X1_54,X0_55,X2_54,X3_54) != iProver_top
    | sP0(X3_54,X2_54,X0_55,X1_54,X0_54) != iProver_top
    | v5_pre_topc(X0_55,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_28,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_454,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1307,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_73,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3313,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1307,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_64,c_65,c_67,c_68,c_69,c_71,c_73,c_2854,c_2904])).

cnf(c_4000,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_3313])).

cnf(c_43,negated_conjecture,
    ( v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_58,plain,
    ( v1_borsuk_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_40,negated_conjecture,
    ( v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_61,plain,
    ( v1_borsuk_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_borsuk_1(X3,X0)
    | ~ v1_borsuk_1(X1,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_458,plain,
    ( sP1(X0_54,X1_54,X0_55,X2_54,X3_54)
    | ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))
    | ~ v1_borsuk_1(X1_54,X0_54)
    | ~ v1_borsuk_1(X2_54,X0_54)
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3387,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),sK5,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_borsuk_1(sK5,sK2)
    | ~ v1_borsuk_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_3391,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_borsuk_1(sK5,sK2) != iProver_top
    | v1_borsuk_1(sK4,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3387])).

cnf(c_3393,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_borsuk_1(sK5,sK2) != iProver_top
    | v1_borsuk_1(sK4,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3391])).

cnf(c_4399,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4000,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_64,c_65,c_67,c_68,c_69,c_71,c_2854,c_2904,c_3393])).

cnf(c_4730,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4575])).

cnf(c_8998,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_4364])).

cnf(c_8999,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8998])).

cnf(c_9001,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8999])).

cnf(c_2618,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(X1_54,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),X1_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_4369,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),X0_54,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_9028,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_4369])).

cnf(c_9029,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9028])).

cnf(c_9031,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9029])).

cnf(c_10008,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9085,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_64,c_65,c_67,c_68,c_69,c_70,c_71,c_2289,c_2854,c_2904,c_4223,c_4399,c_4730,c_9001,c_9031])).

cnf(c_26,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_456,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_55,X1_55)),X0_55)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_55),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_55))
    | ~ v1_funct_2(X1_55,u1_struct_0(X3_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | r1_tsep_1(X0_54,X3_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1305,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_55,X1_55)),X0_55) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_55),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_55)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | r1_tsep_1(X0_54,X3_54) = iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_8285,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1305])).

cnf(c_2169,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,k1_tsep_1(sK2,X0_54,sK5),X0_54,k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_55,X1_55)),X0_55)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,X0_54,k2_tsep_1(sK2,X0_54,sK5),X0_55),k3_tmap_1(sK2,X1_54,sK5,k2_tsep_1(sK2,X0_54,sK5),X1_55))
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_54))
    | r1_tsep_1(X0_54,sK5)
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_2914,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0_54,sK5),X0_54,k10_tmap_1(sK2,sK3,X0_54,sK5,X0_55,sK7)),X0_55)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X0_54,k2_tsep_1(sK2,X0_54,sK5),X0_55),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,X0_54,sK5),sK7))
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | r1_tsep_1(X0_54,sK5)
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_3430,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | r1_tsep_1(sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2914])).

cnf(c_3431,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3430])).

cnf(c_8832,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8285,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_63,c_64,c_65,c_67,c_68,c_69,c_71,c_72,c_3431])).

cnf(c_5114,plain,
    ( sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_1288])).

cnf(c_6293,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5114,c_64,c_65])).

cnf(c_6294,plain,
    ( sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_6293])).

cnf(c_6940,plain,
    ( k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55),sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_6294])).

cnf(c_8920,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55),sK6) != iProver_top
    | k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55) = sK6
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6940,c_54,c_55,c_56])).

cnf(c_8921,plain,
    ( k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55),sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,sK3,X1_54,sK4,X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8920])).

cnf(c_8938,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8832,c_8921])).

cnf(c_4222,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_4220])).

cnf(c_8939,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8938])).

cnf(c_9000,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_8998])).

cnf(c_9097,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8938,c_50,c_49,c_48,c_47,c_46,c_45,c_44,c_42,c_41,c_39,c_37,c_36,c_34,c_33,c_32,c_30,c_2288,c_2853,c_2903,c_4222,c_4731,c_8939,c_9000])).

cnf(c_10012,plain,
    ( v5_pre_topc(sK6,sK4,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10008,c_9097])).

cnf(c_35,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_447,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1314,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_10014,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10012,c_1314])).


%------------------------------------------------------------------------------
