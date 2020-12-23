%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:24 EST 2020

% Result     : Theorem 7.24s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  258 (3416 expanded)
%              Number of clauses        :  174 ( 717 expanded)
%              Number of leaves         :   15 (1345 expanded)
%              Depth                    :   25
%              Number of atoms          : 2830 (74917 expanded)
%              Number of equality atoms :  755 (1865 expanded)
%              Maximal formula depth    :   30 (  11 average)
%              Maximal clause size      :   48 (  10 average)
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
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
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
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
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
                             => ( ( r4_tsep_1(X0,X2,X3)
                                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
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
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r4_tsep_1(X0,X2,X3)
          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & r4_tsep_1(X0,X2,X3)
        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),sK7))
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK7,X3,X1)
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r4_tsep_1(X0,X2,X3)
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
            & r4_tsep_1(X0,X2,X3)
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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r4_tsep_1(X0,X2,X3)
                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
                & r4_tsep_1(X0,X2,sK5)
                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,sK5),X4),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,X2,sK5),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK5,X1)
                & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r4_tsep_1(X0,X2,X3)
                      & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5)) )
                    & r4_tsep_1(X0,sK4,X3)
                    & r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,sK4,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
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
                        & r4_tsep_1(X0,X2,X3)
                        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,sK3,X3,k2_tsep_1(X0,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(X5,X3,sK3)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
                            & r4_tsep_1(X0,X2,X3)
                            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                          & r4_tsep_1(sK2,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r4_tsep_1(sK2,sK4,sK5)
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f43,f42,f41,f40,f39,f38])).

fof(f91,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
    inference(equality_resolution,[],[f47])).

fof(f3,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f26,plain,(
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

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f27,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f34])).

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
                 => ( r4_tsep_1(X0,X2,X3)
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
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
                  | ~ r4_tsep_1(X0,X2,X3)
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

fof(f23,plain,(
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
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(definition_folding,[],[f23,f27,f26])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
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
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
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
    inference(pure_predicate_removal,[],[f4])).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
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

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
    inference(equality_resolution,[],[f48])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_30,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1311,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2048,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_4,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(k10_tmap_1(X2,X1,X0,X3,X4,X5),u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k10_tmap_1(X2,X1,X0,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k10_tmap_1(X2,X1,X0,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1321,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53))
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2038,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_1318,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2041,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_1320,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2039,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_1319,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2040,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_2567,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2038,c_2041,c_2039,c_2040])).

cnf(c_12333,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
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
    inference(superposition,[status(thm)],[c_2048,c_2567])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_52,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_53,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_54,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_55,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_56,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_57,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_58,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_59,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_60,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_62,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_63,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_64,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_66,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_67,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2834,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X1_53,X0_53)) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_3601,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_53,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_5007,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_5008,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5007])).

cnf(c_5010,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
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
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5008])).

cnf(c_2844,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X1_54))
    | v1_funct_2(k10_tmap_1(sK2,X1_54,sK4,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_3761,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54))
    | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_53,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_5052,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3761])).

cnf(c_5053,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5052])).

cnf(c_5055,plain,
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
    inference(instantiation,[status(thm)],[c_5053])).

cnf(c_2854,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | m1_subset_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_3821,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(instantiation,[status(thm)],[c_2854])).

cnf(c_5185,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3821])).

cnf(c_5186,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5185])).

cnf(c_5188,plain,
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
    inference(instantiation,[status(thm)],[c_5186])).

cnf(c_2869,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,k1_tsep_1(sK2,X0_54,sK5),X0_54,k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53)),X0_53)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,X0_54,k2_tsep_1(sK2,X0_54,sK5),X0_53),k3_tmap_1(sK2,X1_54,sK5,k2_tsep_1(sK2,X0_54,sK5),X1_53))
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK5),u1_struct_0(X1_54))
    | ~ v1_funct_2(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_54))))
    | ~ m1_subset_1(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_3922,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,X0_54,sK5,k2_tsep_1(sK2,sK4,sK5),X1_53))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)),X0_53)
    | ~ v1_funct_2(X1_53,u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_5278,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),X0_53)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3922])).

cnf(c_5279,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5278])).

cnf(c_5281,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
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
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5279])).

cnf(c_12391,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12333,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_5010,c_5055,c_5188,c_5281])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X0,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
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
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_515,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | sK5 != X3
    | sK4 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_516,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_520,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | sP1(sK2,sK4,X0,sK5,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_48,c_47,c_46,c_42,c_41,c_40,c_39])).

cnf(c_521,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_520])).

cnf(c_556,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X4,X3,X1)),u1_struct_0(X0))
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X4,X3,X1)),u1_struct_0(X0))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | v2_struct_0(X6)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X1
    | sK4 != X3
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_521])).

cnf(c_557,plain,
    ( sP0(X0,sK5,X1,sK4,sK2)
    | ~ v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_790,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_557])).

cnf(c_791,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_790])).

cnf(c_1288,plain,
    ( ~ v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_791])).

cnf(c_2071,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1317,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(k1_tsep_1(X1_54,X2_54,X0_54),X1_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2780,plain,
    ( ~ m1_pre_topc(X0_54,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_54,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_2963,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_2964,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2963])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_1315,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2824,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k3_tmap_1(sK2,X1_54,X0_54,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_3447,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_3448,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3447])).

cnf(c_11136,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2071,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,c_3448])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1324,plain,
    ( ~ r2_funct_2(X0_55,X1_55,X0_53,X1_53)
    | ~ v1_funct_2(X1_53,X0_55,X1_55)
    | ~ v1_funct_2(X0_53,X0_55,X1_55)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | X0_53 = X1_53 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2035,plain,
    ( X0_53 = X1_53
    | r2_funct_2(X0_55,X1_55,X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_53,X0_55,X1_55) != iProver_top
    | v1_funct_2(X1_53,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_11151,plain,
    ( k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53) = X1_53
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),X1_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11136,c_2035])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_700,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_557])).

cnf(c_701,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_1291,plain,
    ( ~ v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) ),
    inference(subtyping,[status(esa)],[c_701])).

cnf(c_2068,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1291])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_1313,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2804,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(sK2,X1_54,X0_54,sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_3327,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2804])).

cnf(c_3328,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3327])).

cnf(c_10144,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2068,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,c_3328])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_730,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_557])).

cnf(c_731,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_1290,plain,
    ( ~ v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_731])).

cnf(c_2069,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1290])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_1314,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2814,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(sK2,X1_54,X0_54,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_3387,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_3388,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3387])).

cnf(c_10742,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2069,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,c_3388])).

cnf(c_12505,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53) = X1_53
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),X1_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11151,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,c_3328,c_3388])).

cnf(c_12506,plain,
    ( k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53) = X1_53
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),X1_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_12505])).

cnf(c_12522,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12391,c_12506])).

cnf(c_2044,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_7033,plain,
    ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
    | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2035])).

cnf(c_2046,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_2045,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_11019,plain,
    ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
    | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7033,c_2046,c_2045])).

cnf(c_12396,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12391,c_11019])).

cnf(c_12622,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12522,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_2964,c_5010,c_5055,c_5188,c_12396])).

cnf(c_3,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(k10_tmap_1(X2,X1,X3,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(k10_tmap_1(X2,X1,X3,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k10_tmap_1(X2,X1,X3,X0,X4,X5)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1322,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53))
    | ~ v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2037,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_2527,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2037,c_2041,c_2039,c_2040])).

cnf(c_11684,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
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
    inference(superposition,[status(thm)],[c_2048,c_2527])).

cnf(c_2884,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,k1_tsep_1(sK2,sK4,X0_54),X0_54,k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53)),X1_53)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,sK4,k2_tsep_1(sK2,sK4,X0_54),X0_53),k3_tmap_1(sK2,X1_54,X0_54,k2_tsep_1(sK2,sK4,X0_54),X1_53))
    | ~ v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(X1_54))
    | ~ v1_funct_2(k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | ~ m1_subset_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_4005,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,X0_54,sK5,k2_tsep_1(sK2,sK4,sK5),X1_53))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)),X1_53)
    | ~ v1_funct_2(X1_53,u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_2884])).

cnf(c_5350,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),sK7)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4005])).

cnf(c_5351,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),sK7) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5350])).

cnf(c_5353,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
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
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5351])).

cnf(c_11972,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11684,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_5010,c_5055,c_5188,c_5353])).

cnf(c_11978,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_11972,c_11019])).

cnf(c_12173,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11978,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_2964,c_5010,c_5055,c_5188])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_590,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | v2_struct_0(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X1
    | sK4 != X3
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_521])).

cnf(c_591,plain,
    ( ~ sP0(X0,sK5,X1,sK4,sK2)
    | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_649,plain,
    ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),X5,X3)
    | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),X4,X3)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
    | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6))
    | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_591])).

cnf(c_650,plain,
    ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),sK5,X1)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),sK4,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0))
    | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_1292,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | v2_struct_0(X0_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53))
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) ),
    inference(subtyping,[status(esa)],[c_650])).

cnf(c_2067,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_1396,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_2799,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(sK2,X1_54,X0_54,sK5,X0_53)) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_3297,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2799])).

cnf(c_3298,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3297])).

cnf(c_2809,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(sK2,X1_54,X0_54,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_3357,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_2809])).

cnf(c_3358,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3357])).

cnf(c_2819,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k3_tmap_1(sK2,X1_54,X0_54,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_3417,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_3418,plain,
    ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3417])).

cnf(c_9664,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_1396,c_2964,c_3298,c_3328,c_3358,c_3388,c_3418,c_3448])).

cnf(c_12182,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12173,c_9664])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_65,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_69,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12308,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12182,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_65,c_66,c_69,c_5010,c_5055,c_5188])).

cnf(c_12626,plain,
    ( v5_pre_topc(sK6,sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12622,c_12308])).

cnf(c_36,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_61,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12626,c_61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:48:27 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.24/1.44  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/1.44  
% 7.24/1.44  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.24/1.44  
% 7.24/1.44  ------  iProver source info
% 7.24/1.44  
% 7.24/1.44  git: date: 2020-06-30 10:37:57 +0100
% 7.24/1.44  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.24/1.44  git: non_committed_changes: false
% 7.24/1.44  git: last_make_outside_of_git: false
% 7.24/1.44  
% 7.24/1.44  ------ 
% 7.24/1.44  
% 7.24/1.44  ------ Input Options
% 7.24/1.44  
% 7.24/1.44  --out_options                           all
% 7.24/1.44  --tptp_safe_out                         true
% 7.24/1.44  --problem_path                          ""
% 7.24/1.44  --include_path                          ""
% 7.24/1.44  --clausifier                            res/vclausify_rel
% 7.24/1.44  --clausifier_options                    --mode clausify
% 7.24/1.44  --stdin                                 false
% 7.24/1.44  --stats_out                             all
% 7.24/1.44  
% 7.24/1.44  ------ General Options
% 7.24/1.44  
% 7.24/1.44  --fof                                   false
% 7.24/1.44  --time_out_real                         305.
% 7.24/1.44  --time_out_virtual                      -1.
% 7.24/1.44  --symbol_type_check                     false
% 7.24/1.44  --clausify_out                          false
% 7.24/1.44  --sig_cnt_out                           false
% 7.24/1.44  --trig_cnt_out                          false
% 7.24/1.44  --trig_cnt_out_tolerance                1.
% 7.24/1.44  --trig_cnt_out_sk_spl                   false
% 7.24/1.44  --abstr_cl_out                          false
% 7.24/1.44  
% 7.24/1.44  ------ Global Options
% 7.24/1.44  
% 7.24/1.44  --schedule                              default
% 7.24/1.44  --add_important_lit                     false
% 7.24/1.44  --prop_solver_per_cl                    1000
% 7.24/1.44  --min_unsat_core                        false
% 7.24/1.44  --soft_assumptions                      false
% 7.24/1.44  --soft_lemma_size                       3
% 7.24/1.44  --prop_impl_unit_size                   0
% 7.24/1.44  --prop_impl_unit                        []
% 7.24/1.44  --share_sel_clauses                     true
% 7.24/1.44  --reset_solvers                         false
% 7.24/1.44  --bc_imp_inh                            [conj_cone]
% 7.24/1.44  --conj_cone_tolerance                   3.
% 7.24/1.44  --extra_neg_conj                        none
% 7.24/1.44  --large_theory_mode                     true
% 7.24/1.44  --prolific_symb_bound                   200
% 7.24/1.44  --lt_threshold                          2000
% 7.24/1.44  --clause_weak_htbl                      true
% 7.24/1.44  --gc_record_bc_elim                     false
% 7.24/1.44  
% 7.24/1.44  ------ Preprocessing Options
% 7.24/1.44  
% 7.24/1.44  --preprocessing_flag                    true
% 7.24/1.44  --time_out_prep_mult                    0.1
% 7.24/1.44  --splitting_mode                        input
% 7.24/1.44  --splitting_grd                         true
% 7.24/1.44  --splitting_cvd                         false
% 7.24/1.44  --splitting_cvd_svl                     false
% 7.24/1.44  --splitting_nvd                         32
% 7.24/1.44  --sub_typing                            true
% 7.24/1.44  --prep_gs_sim                           true
% 7.24/1.44  --prep_unflatten                        true
% 7.24/1.44  --prep_res_sim                          true
% 7.24/1.44  --prep_upred                            true
% 7.24/1.44  --prep_sem_filter                       exhaustive
% 7.24/1.44  --prep_sem_filter_out                   false
% 7.24/1.44  --pred_elim                             true
% 7.24/1.44  --res_sim_input                         true
% 7.24/1.44  --eq_ax_congr_red                       true
% 7.24/1.44  --pure_diseq_elim                       true
% 7.24/1.44  --brand_transform                       false
% 7.24/1.44  --non_eq_to_eq                          false
% 7.24/1.44  --prep_def_merge                        true
% 7.24/1.44  --prep_def_merge_prop_impl              false
% 7.24/1.44  --prep_def_merge_mbd                    true
% 7.24/1.44  --prep_def_merge_tr_red                 false
% 7.24/1.44  --prep_def_merge_tr_cl                  false
% 7.24/1.44  --smt_preprocessing                     true
% 7.24/1.44  --smt_ac_axioms                         fast
% 7.24/1.44  --preprocessed_out                      false
% 7.24/1.44  --preprocessed_stats                    false
% 7.24/1.44  
% 7.24/1.44  ------ Abstraction refinement Options
% 7.24/1.44  
% 7.24/1.44  --abstr_ref                             []
% 7.24/1.44  --abstr_ref_prep                        false
% 7.24/1.44  --abstr_ref_until_sat                   false
% 7.24/1.44  --abstr_ref_sig_restrict                funpre
% 7.24/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.44  --abstr_ref_under                       []
% 7.24/1.44  
% 7.24/1.44  ------ SAT Options
% 7.24/1.44  
% 7.24/1.44  --sat_mode                              false
% 7.24/1.44  --sat_fm_restart_options                ""
% 7.24/1.44  --sat_gr_def                            false
% 7.24/1.44  --sat_epr_types                         true
% 7.24/1.44  --sat_non_cyclic_types                  false
% 7.24/1.44  --sat_finite_models                     false
% 7.24/1.44  --sat_fm_lemmas                         false
% 7.24/1.44  --sat_fm_prep                           false
% 7.24/1.44  --sat_fm_uc_incr                        true
% 7.24/1.44  --sat_out_model                         small
% 7.24/1.44  --sat_out_clauses                       false
% 7.24/1.44  
% 7.24/1.44  ------ QBF Options
% 7.24/1.44  
% 7.24/1.44  --qbf_mode                              false
% 7.24/1.44  --qbf_elim_univ                         false
% 7.24/1.44  --qbf_dom_inst                          none
% 7.24/1.44  --qbf_dom_pre_inst                      false
% 7.24/1.44  --qbf_sk_in                             false
% 7.24/1.44  --qbf_pred_elim                         true
% 7.24/1.44  --qbf_split                             512
% 7.24/1.44  
% 7.24/1.44  ------ BMC1 Options
% 7.24/1.44  
% 7.24/1.44  --bmc1_incremental                      false
% 7.24/1.44  --bmc1_axioms                           reachable_all
% 7.24/1.44  --bmc1_min_bound                        0
% 7.24/1.44  --bmc1_max_bound                        -1
% 7.24/1.44  --bmc1_max_bound_default                -1
% 7.24/1.44  --bmc1_symbol_reachability              true
% 7.24/1.44  --bmc1_property_lemmas                  false
% 7.24/1.44  --bmc1_k_induction                      false
% 7.24/1.44  --bmc1_non_equiv_states                 false
% 7.24/1.44  --bmc1_deadlock                         false
% 7.24/1.44  --bmc1_ucm                              false
% 7.24/1.44  --bmc1_add_unsat_core                   none
% 7.24/1.44  --bmc1_unsat_core_children              false
% 7.24/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.44  --bmc1_out_stat                         full
% 7.24/1.44  --bmc1_ground_init                      false
% 7.24/1.44  --bmc1_pre_inst_next_state              false
% 7.24/1.44  --bmc1_pre_inst_state                   false
% 7.24/1.44  --bmc1_pre_inst_reach_state             false
% 7.24/1.44  --bmc1_out_unsat_core                   false
% 7.24/1.44  --bmc1_aig_witness_out                  false
% 7.24/1.44  --bmc1_verbose                          false
% 7.24/1.44  --bmc1_dump_clauses_tptp                false
% 7.24/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.44  --bmc1_dump_file                        -
% 7.24/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.44  --bmc1_ucm_extend_mode                  1
% 7.24/1.44  --bmc1_ucm_init_mode                    2
% 7.24/1.44  --bmc1_ucm_cone_mode                    none
% 7.24/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.44  --bmc1_ucm_relax_model                  4
% 7.24/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.44  --bmc1_ucm_layered_model                none
% 7.24/1.44  --bmc1_ucm_max_lemma_size               10
% 7.24/1.44  
% 7.24/1.44  ------ AIG Options
% 7.24/1.44  
% 7.24/1.44  --aig_mode                              false
% 7.24/1.44  
% 7.24/1.44  ------ Instantiation Options
% 7.24/1.44  
% 7.24/1.44  --instantiation_flag                    true
% 7.24/1.44  --inst_sos_flag                         false
% 7.24/1.44  --inst_sos_phase                        true
% 7.24/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.44  --inst_lit_sel_side                     num_symb
% 7.24/1.44  --inst_solver_per_active                1400
% 7.24/1.44  --inst_solver_calls_frac                1.
% 7.24/1.44  --inst_passive_queue_type               priority_queues
% 7.24/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.44  --inst_passive_queues_freq              [25;2]
% 7.24/1.44  --inst_dismatching                      true
% 7.24/1.44  --inst_eager_unprocessed_to_passive     true
% 7.24/1.44  --inst_prop_sim_given                   true
% 7.24/1.44  --inst_prop_sim_new                     false
% 7.24/1.44  --inst_subs_new                         false
% 7.24/1.44  --inst_eq_res_simp                      false
% 7.24/1.44  --inst_subs_given                       false
% 7.24/1.44  --inst_orphan_elimination               true
% 7.24/1.44  --inst_learning_loop_flag               true
% 7.24/1.44  --inst_learning_start                   3000
% 7.24/1.44  --inst_learning_factor                  2
% 7.24/1.44  --inst_start_prop_sim_after_learn       3
% 7.24/1.44  --inst_sel_renew                        solver
% 7.24/1.44  --inst_lit_activity_flag                true
% 7.24/1.44  --inst_restr_to_given                   false
% 7.24/1.44  --inst_activity_threshold               500
% 7.24/1.44  --inst_out_proof                        true
% 7.24/1.44  
% 7.24/1.44  ------ Resolution Options
% 7.24/1.44  
% 7.24/1.44  --resolution_flag                       true
% 7.24/1.44  --res_lit_sel                           adaptive
% 7.24/1.44  --res_lit_sel_side                      none
% 7.24/1.44  --res_ordering                          kbo
% 7.24/1.44  --res_to_prop_solver                    active
% 7.24/1.44  --res_prop_simpl_new                    false
% 7.24/1.44  --res_prop_simpl_given                  true
% 7.24/1.44  --res_passive_queue_type                priority_queues
% 7.24/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.44  --res_passive_queues_freq               [15;5]
% 7.24/1.44  --res_forward_subs                      full
% 7.24/1.44  --res_backward_subs                     full
% 7.24/1.44  --res_forward_subs_resolution           true
% 7.24/1.44  --res_backward_subs_resolution          true
% 7.24/1.44  --res_orphan_elimination                true
% 7.24/1.44  --res_time_limit                        2.
% 7.24/1.44  --res_out_proof                         true
% 7.24/1.44  
% 7.24/1.44  ------ Superposition Options
% 7.24/1.44  
% 7.24/1.44  --superposition_flag                    true
% 7.24/1.44  --sup_passive_queue_type                priority_queues
% 7.24/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.44  --demod_completeness_check              fast
% 7.24/1.44  --demod_use_ground                      true
% 7.24/1.44  --sup_to_prop_solver                    passive
% 7.24/1.44  --sup_prop_simpl_new                    true
% 7.24/1.44  --sup_prop_simpl_given                  true
% 7.24/1.44  --sup_fun_splitting                     false
% 7.24/1.44  --sup_smt_interval                      50000
% 7.24/1.44  
% 7.24/1.44  ------ Superposition Simplification Setup
% 7.24/1.44  
% 7.24/1.44  --sup_indices_passive                   []
% 7.24/1.44  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.44  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.44  --sup_full_bw                           [BwDemod]
% 7.24/1.44  --sup_immed_triv                        [TrivRules]
% 7.24/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.44  --sup_immed_bw_main                     []
% 7.24/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.44  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.44  
% 7.24/1.44  ------ Combination Options
% 7.24/1.44  
% 7.24/1.44  --comb_res_mult                         3
% 7.24/1.44  --comb_sup_mult                         2
% 7.24/1.44  --comb_inst_mult                        10
% 7.24/1.44  
% 7.24/1.44  ------ Debug Options
% 7.24/1.44  
% 7.24/1.44  --dbg_backtrace                         false
% 7.24/1.44  --dbg_dump_prop_clauses                 false
% 7.24/1.44  --dbg_dump_prop_clauses_file            -
% 7.24/1.44  --dbg_out_stat                          false
% 7.24/1.44  ------ Parsing...
% 7.24/1.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.24/1.44  
% 7.24/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.24/1.44  
% 7.24/1.44  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.24/1.44  
% 7.24/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.24/1.44  ------ Proving...
% 7.24/1.44  ------ Problem Properties 
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  clauses                                 42
% 7.24/1.44  conjectures                             20
% 7.24/1.44  EPR                                     14
% 7.24/1.44  Horn                                    22
% 7.24/1.44  unary                                   19
% 7.24/1.44  binary                                  0
% 7.24/1.44  lits                                    280
% 7.24/1.44  lits eq                                 2
% 7.24/1.44  fd_pure                                 0
% 7.24/1.44  fd_pseudo                               0
% 7.24/1.44  fd_cond                                 0
% 7.24/1.44  fd_pseudo_cond                          2
% 7.24/1.44  AC symbols                              0
% 7.24/1.44  
% 7.24/1.44  ------ Schedule dynamic 5 is on 
% 7.24/1.44  
% 7.24/1.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  ------ 
% 7.24/1.44  Current options:
% 7.24/1.44  ------ 
% 7.24/1.44  
% 7.24/1.44  ------ Input Options
% 7.24/1.44  
% 7.24/1.44  --out_options                           all
% 7.24/1.44  --tptp_safe_out                         true
% 7.24/1.44  --problem_path                          ""
% 7.24/1.44  --include_path                          ""
% 7.24/1.44  --clausifier                            res/vclausify_rel
% 7.24/1.44  --clausifier_options                    --mode clausify
% 7.24/1.44  --stdin                                 false
% 7.24/1.44  --stats_out                             all
% 7.24/1.44  
% 7.24/1.44  ------ General Options
% 7.24/1.44  
% 7.24/1.44  --fof                                   false
% 7.24/1.44  --time_out_real                         305.
% 7.24/1.44  --time_out_virtual                      -1.
% 7.24/1.44  --symbol_type_check                     false
% 7.24/1.44  --clausify_out                          false
% 7.24/1.44  --sig_cnt_out                           false
% 7.24/1.44  --trig_cnt_out                          false
% 7.24/1.44  --trig_cnt_out_tolerance                1.
% 7.24/1.44  --trig_cnt_out_sk_spl                   false
% 7.24/1.44  --abstr_cl_out                          false
% 7.24/1.44  
% 7.24/1.44  ------ Global Options
% 7.24/1.44  
% 7.24/1.44  --schedule                              default
% 7.24/1.44  --add_important_lit                     false
% 7.24/1.44  --prop_solver_per_cl                    1000
% 7.24/1.44  --min_unsat_core                        false
% 7.24/1.44  --soft_assumptions                      false
% 7.24/1.44  --soft_lemma_size                       3
% 7.24/1.44  --prop_impl_unit_size                   0
% 7.24/1.44  --prop_impl_unit                        []
% 7.24/1.44  --share_sel_clauses                     true
% 7.24/1.44  --reset_solvers                         false
% 7.24/1.44  --bc_imp_inh                            [conj_cone]
% 7.24/1.44  --conj_cone_tolerance                   3.
% 7.24/1.44  --extra_neg_conj                        none
% 7.24/1.44  --large_theory_mode                     true
% 7.24/1.44  --prolific_symb_bound                   200
% 7.24/1.44  --lt_threshold                          2000
% 7.24/1.44  --clause_weak_htbl                      true
% 7.24/1.44  --gc_record_bc_elim                     false
% 7.24/1.44  
% 7.24/1.44  ------ Preprocessing Options
% 7.24/1.44  
% 7.24/1.44  --preprocessing_flag                    true
% 7.24/1.44  --time_out_prep_mult                    0.1
% 7.24/1.44  --splitting_mode                        input
% 7.24/1.44  --splitting_grd                         true
% 7.24/1.44  --splitting_cvd                         false
% 7.24/1.44  --splitting_cvd_svl                     false
% 7.24/1.44  --splitting_nvd                         32
% 7.24/1.44  --sub_typing                            true
% 7.24/1.44  --prep_gs_sim                           true
% 7.24/1.44  --prep_unflatten                        true
% 7.24/1.44  --prep_res_sim                          true
% 7.24/1.44  --prep_upred                            true
% 7.24/1.44  --prep_sem_filter                       exhaustive
% 7.24/1.44  --prep_sem_filter_out                   false
% 7.24/1.44  --pred_elim                             true
% 7.24/1.44  --res_sim_input                         true
% 7.24/1.44  --eq_ax_congr_red                       true
% 7.24/1.44  --pure_diseq_elim                       true
% 7.24/1.44  --brand_transform                       false
% 7.24/1.44  --non_eq_to_eq                          false
% 7.24/1.44  --prep_def_merge                        true
% 7.24/1.44  --prep_def_merge_prop_impl              false
% 7.24/1.44  --prep_def_merge_mbd                    true
% 7.24/1.44  --prep_def_merge_tr_red                 false
% 7.24/1.44  --prep_def_merge_tr_cl                  false
% 7.24/1.44  --smt_preprocessing                     true
% 7.24/1.44  --smt_ac_axioms                         fast
% 7.24/1.44  --preprocessed_out                      false
% 7.24/1.44  --preprocessed_stats                    false
% 7.24/1.44  
% 7.24/1.44  ------ Abstraction refinement Options
% 7.24/1.44  
% 7.24/1.44  --abstr_ref                             []
% 7.24/1.44  --abstr_ref_prep                        false
% 7.24/1.44  --abstr_ref_until_sat                   false
% 7.24/1.44  --abstr_ref_sig_restrict                funpre
% 7.24/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.44  --abstr_ref_under                       []
% 7.24/1.44  
% 7.24/1.44  ------ SAT Options
% 7.24/1.44  
% 7.24/1.44  --sat_mode                              false
% 7.24/1.44  --sat_fm_restart_options                ""
% 7.24/1.44  --sat_gr_def                            false
% 7.24/1.44  --sat_epr_types                         true
% 7.24/1.44  --sat_non_cyclic_types                  false
% 7.24/1.44  --sat_finite_models                     false
% 7.24/1.44  --sat_fm_lemmas                         false
% 7.24/1.44  --sat_fm_prep                           false
% 7.24/1.44  --sat_fm_uc_incr                        true
% 7.24/1.44  --sat_out_model                         small
% 7.24/1.44  --sat_out_clauses                       false
% 7.24/1.44  
% 7.24/1.44  ------ QBF Options
% 7.24/1.44  
% 7.24/1.44  --qbf_mode                              false
% 7.24/1.44  --qbf_elim_univ                         false
% 7.24/1.44  --qbf_dom_inst                          none
% 7.24/1.44  --qbf_dom_pre_inst                      false
% 7.24/1.44  --qbf_sk_in                             false
% 7.24/1.44  --qbf_pred_elim                         true
% 7.24/1.44  --qbf_split                             512
% 7.24/1.44  
% 7.24/1.44  ------ BMC1 Options
% 7.24/1.44  
% 7.24/1.44  --bmc1_incremental                      false
% 7.24/1.44  --bmc1_axioms                           reachable_all
% 7.24/1.44  --bmc1_min_bound                        0
% 7.24/1.44  --bmc1_max_bound                        -1
% 7.24/1.44  --bmc1_max_bound_default                -1
% 7.24/1.44  --bmc1_symbol_reachability              true
% 7.24/1.44  --bmc1_property_lemmas                  false
% 7.24/1.44  --bmc1_k_induction                      false
% 7.24/1.44  --bmc1_non_equiv_states                 false
% 7.24/1.44  --bmc1_deadlock                         false
% 7.24/1.44  --bmc1_ucm                              false
% 7.24/1.44  --bmc1_add_unsat_core                   none
% 7.24/1.44  --bmc1_unsat_core_children              false
% 7.24/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.44  --bmc1_out_stat                         full
% 7.24/1.44  --bmc1_ground_init                      false
% 7.24/1.44  --bmc1_pre_inst_next_state              false
% 7.24/1.44  --bmc1_pre_inst_state                   false
% 7.24/1.44  --bmc1_pre_inst_reach_state             false
% 7.24/1.44  --bmc1_out_unsat_core                   false
% 7.24/1.44  --bmc1_aig_witness_out                  false
% 7.24/1.44  --bmc1_verbose                          false
% 7.24/1.44  --bmc1_dump_clauses_tptp                false
% 7.24/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.44  --bmc1_dump_file                        -
% 7.24/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.44  --bmc1_ucm_extend_mode                  1
% 7.24/1.44  --bmc1_ucm_init_mode                    2
% 7.24/1.44  --bmc1_ucm_cone_mode                    none
% 7.24/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.44  --bmc1_ucm_relax_model                  4
% 7.24/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.44  --bmc1_ucm_layered_model                none
% 7.24/1.44  --bmc1_ucm_max_lemma_size               10
% 7.24/1.44  
% 7.24/1.44  ------ AIG Options
% 7.24/1.44  
% 7.24/1.44  --aig_mode                              false
% 7.24/1.44  
% 7.24/1.44  ------ Instantiation Options
% 7.24/1.44  
% 7.24/1.44  --instantiation_flag                    true
% 7.24/1.44  --inst_sos_flag                         false
% 7.24/1.44  --inst_sos_phase                        true
% 7.24/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.44  --inst_lit_sel_side                     none
% 7.24/1.44  --inst_solver_per_active                1400
% 7.24/1.44  --inst_solver_calls_frac                1.
% 7.24/1.44  --inst_passive_queue_type               priority_queues
% 7.24/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.44  --inst_passive_queues_freq              [25;2]
% 7.24/1.44  --inst_dismatching                      true
% 7.24/1.44  --inst_eager_unprocessed_to_passive     true
% 7.24/1.44  --inst_prop_sim_given                   true
% 7.24/1.44  --inst_prop_sim_new                     false
% 7.24/1.44  --inst_subs_new                         false
% 7.24/1.44  --inst_eq_res_simp                      false
% 7.24/1.44  --inst_subs_given                       false
% 7.24/1.44  --inst_orphan_elimination               true
% 7.24/1.44  --inst_learning_loop_flag               true
% 7.24/1.44  --inst_learning_start                   3000
% 7.24/1.44  --inst_learning_factor                  2
% 7.24/1.44  --inst_start_prop_sim_after_learn       3
% 7.24/1.44  --inst_sel_renew                        solver
% 7.24/1.44  --inst_lit_activity_flag                true
% 7.24/1.44  --inst_restr_to_given                   false
% 7.24/1.44  --inst_activity_threshold               500
% 7.24/1.44  --inst_out_proof                        true
% 7.24/1.44  
% 7.24/1.44  ------ Resolution Options
% 7.24/1.44  
% 7.24/1.44  --resolution_flag                       false
% 7.24/1.44  --res_lit_sel                           adaptive
% 7.24/1.44  --res_lit_sel_side                      none
% 7.24/1.44  --res_ordering                          kbo
% 7.24/1.44  --res_to_prop_solver                    active
% 7.24/1.44  --res_prop_simpl_new                    false
% 7.24/1.44  --res_prop_simpl_given                  true
% 7.24/1.44  --res_passive_queue_type                priority_queues
% 7.24/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.44  --res_passive_queues_freq               [15;5]
% 7.24/1.44  --res_forward_subs                      full
% 7.24/1.44  --res_backward_subs                     full
% 7.24/1.44  --res_forward_subs_resolution           true
% 7.24/1.44  --res_backward_subs_resolution          true
% 7.24/1.44  --res_orphan_elimination                true
% 7.24/1.44  --res_time_limit                        2.
% 7.24/1.44  --res_out_proof                         true
% 7.24/1.44  
% 7.24/1.44  ------ Superposition Options
% 7.24/1.44  
% 7.24/1.44  --superposition_flag                    true
% 7.24/1.44  --sup_passive_queue_type                priority_queues
% 7.24/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.44  --demod_completeness_check              fast
% 7.24/1.44  --demod_use_ground                      true
% 7.24/1.44  --sup_to_prop_solver                    passive
% 7.24/1.44  --sup_prop_simpl_new                    true
% 7.24/1.44  --sup_prop_simpl_given                  true
% 7.24/1.44  --sup_fun_splitting                     false
% 7.24/1.44  --sup_smt_interval                      50000
% 7.24/1.44  
% 7.24/1.44  ------ Superposition Simplification Setup
% 7.24/1.44  
% 7.24/1.44  --sup_indices_passive                   []
% 7.24/1.44  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.44  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.44  --sup_full_bw                           [BwDemod]
% 7.24/1.44  --sup_immed_triv                        [TrivRules]
% 7.24/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.44  --sup_immed_bw_main                     []
% 7.24/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.44  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.44  
% 7.24/1.44  ------ Combination Options
% 7.24/1.44  
% 7.24/1.44  --comb_res_mult                         3
% 7.24/1.44  --comb_sup_mult                         2
% 7.24/1.44  --comb_inst_mult                        10
% 7.24/1.44  
% 7.24/1.44  ------ Debug Options
% 7.24/1.44  
% 7.24/1.44  --dbg_backtrace                         false
% 7.24/1.44  --dbg_dump_prop_clauses                 false
% 7.24/1.44  --dbg_dump_prop_clauses_file            -
% 7.24/1.44  --dbg_out_stat                          false
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  ------ Proving...
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  % SZS status Theorem for theBenchmark.p
% 7.24/1.44  
% 7.24/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 7.24/1.44  
% 7.24/1.44  fof(f7,conjecture,(
% 7.24/1.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 7.24/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.44  
% 7.24/1.44  fof(f8,negated_conjecture,(
% 7.24/1.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 7.24/1.44    inference(negated_conjecture,[],[f7])).
% 7.24/1.44  
% 7.24/1.44  fof(f11,plain,(
% 7.24/1.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 7.24/1.44    inference(pure_predicate_removal,[],[f8])).
% 7.24/1.44  
% 7.24/1.44  fof(f24,plain,(
% 7.24/1.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.24/1.44    inference(ennf_transformation,[],[f11])).
% 7.24/1.44  
% 7.24/1.44  fof(f25,plain,(
% 7.24/1.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.24/1.44    inference(flattening,[],[f24])).
% 7.24/1.44  
% 7.24/1.44  fof(f43,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 7.24/1.44    introduced(choice_axiom,[])).
% 7.24/1.44  
% 7.24/1.44  fof(f42,plain,(
% 7.24/1.44    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),sK6),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 7.24/1.44    introduced(choice_axiom,[])).
% 7.24/1.44  
% 7.24/1.44  fof(f41,plain,(
% 7.24/1.44    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r4_tsep_1(X0,X2,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,sK5),X4),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,X2,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.24/1.44    introduced(choice_axiom,[])).
% 7.24/1.44  
% 7.24/1.44  fof(f40,plain,(
% 7.24/1.44    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r4_tsep_1(X0,sK4,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,sK4,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 7.24/1.44    introduced(choice_axiom,[])).
% 7.24/1.44  
% 7.24/1.44  fof(f39,plain,(
% 7.24/1.44    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,sK3,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.24/1.44    introduced(choice_axiom,[])).
% 7.24/1.44  
% 7.24/1.44  fof(f38,plain,(
% 7.24/1.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.24/1.44    introduced(choice_axiom,[])).
% 7.24/1.44  
% 7.24/1.44  fof(f44,plain,(
% 7.24/1.44    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.24/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f43,f42,f41,f40,f39,f38])).
% 7.24/1.44  
% 7.24/1.44  fof(f91,plain,(
% 7.24/1.44    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f2,axiom,(
% 7.24/1.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r1_tsep_1(X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 7.24/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.44  
% 7.24/1.44  fof(f10,plain,(
% 7.24/1.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 7.24/1.44    inference(pure_predicate_removal,[],[f2])).
% 7.24/1.44  
% 7.24/1.44  fof(f14,plain,(
% 7.24/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6))) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.24/1.44    inference(ennf_transformation,[],[f10])).
% 7.24/1.44  
% 7.24/1.44  fof(f15,plain,(
% 7.24/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(flattening,[],[f14])).
% 7.24/1.44  
% 7.24/1.44  fof(f30,plain,(
% 7.24/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(nnf_transformation,[],[f15])).
% 7.24/1.44  
% 7.24/1.44  fof(f31,plain,(
% 7.24/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(flattening,[],[f30])).
% 7.24/1.44  
% 7.24/1.44  fof(f47,plain,(
% 7.24/1.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f31])).
% 7.24/1.44  
% 7.24/1.44  fof(f96,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(equality_resolution,[],[f47])).
% 7.24/1.44  
% 7.24/1.44  fof(f3,axiom,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.24/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.44  
% 7.24/1.44  fof(f16,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.24/1.44    inference(ennf_transformation,[],[f3])).
% 7.24/1.44  
% 7.24/1.44  fof(f17,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(flattening,[],[f16])).
% 7.24/1.44  
% 7.24/1.44  fof(f50,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f17])).
% 7.24/1.44  
% 7.24/1.44  fof(f52,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f17])).
% 7.24/1.44  
% 7.24/1.44  fof(f51,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f17])).
% 7.24/1.44  
% 7.24/1.44  fof(f73,plain,(
% 7.24/1.44    ~v2_struct_0(sK2)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f74,plain,(
% 7.24/1.44    v2_pre_topc(sK2)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f75,plain,(
% 7.24/1.44    l1_pre_topc(sK2)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f76,plain,(
% 7.24/1.44    ~v2_struct_0(sK3)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f77,plain,(
% 7.24/1.44    v2_pre_topc(sK3)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f78,plain,(
% 7.24/1.44    l1_pre_topc(sK3)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f79,plain,(
% 7.24/1.44    ~v2_struct_0(sK4)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f80,plain,(
% 7.24/1.44    m1_pre_topc(sK4,sK2)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f81,plain,(
% 7.24/1.44    ~v2_struct_0(sK5)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f82,plain,(
% 7.24/1.44    m1_pre_topc(sK5,sK2)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f83,plain,(
% 7.24/1.44    v1_funct_1(sK6)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f84,plain,(
% 7.24/1.44    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f86,plain,(
% 7.24/1.44    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f87,plain,(
% 7.24/1.44    v1_funct_1(sK7)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f88,plain,(
% 7.24/1.44    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f90,plain,(
% 7.24/1.44    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f26,plain,(
% 7.24/1.44    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 7.24/1.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.24/1.44  
% 7.24/1.44  fof(f35,plain,(
% 7.24/1.44    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 7.24/1.44    inference(nnf_transformation,[],[f26])).
% 7.24/1.44  
% 7.24/1.44  fof(f36,plain,(
% 7.24/1.44    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 7.24/1.44    inference(flattening,[],[f35])).
% 7.24/1.44  
% 7.24/1.44  fof(f37,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.24/1.44    inference(rectify,[],[f36])).
% 7.24/1.44  
% 7.24/1.44  fof(f66,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f37])).
% 7.24/1.44  
% 7.24/1.44  fof(f27,plain,(
% 7.24/1.44    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 7.24/1.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.24/1.44  
% 7.24/1.44  fof(f32,plain,(
% 7.24/1.44    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 7.24/1.44    inference(nnf_transformation,[],[f27])).
% 7.24/1.44  
% 7.24/1.44  fof(f33,plain,(
% 7.24/1.44    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 7.24/1.44    inference(flattening,[],[f32])).
% 7.24/1.44  
% 7.24/1.44  fof(f34,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.24/1.44    inference(rectify,[],[f33])).
% 7.24/1.44  
% 7.24/1.44  fof(f58,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f34])).
% 7.24/1.44  
% 7.24/1.44  fof(f6,axiom,(
% 7.24/1.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 7.24/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.44  
% 7.24/1.44  fof(f22,plain,(
% 7.24/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.24/1.44    inference(ennf_transformation,[],[f6])).
% 7.24/1.44  
% 7.24/1.44  fof(f23,plain,(
% 7.24/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(flattening,[],[f22])).
% 7.24/1.44  
% 7.24/1.44  fof(f28,plain,(
% 7.24/1.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(definition_folding,[],[f23,f27,f26])).
% 7.24/1.44  
% 7.24/1.44  fof(f72,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f28])).
% 7.24/1.44  
% 7.24/1.44  fof(f92,plain,(
% 7.24/1.44    r4_tsep_1(sK2,sK4,sK5)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f4,axiom,(
% 7.24/1.44    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.24/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.44  
% 7.24/1.44  fof(f9,plain,(
% 7.24/1.44    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 7.24/1.44    inference(pure_predicate_removal,[],[f4])).
% 7.24/1.44  
% 7.24/1.44  fof(f18,plain,(
% 7.24/1.44    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.24/1.44    inference(ennf_transformation,[],[f9])).
% 7.24/1.44  
% 7.24/1.44  fof(f19,plain,(
% 7.24/1.44    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(flattening,[],[f18])).
% 7.24/1.44  
% 7.24/1.44  fof(f54,plain,(
% 7.24/1.44    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f19])).
% 7.24/1.44  
% 7.24/1.44  fof(f5,axiom,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.24/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.44  
% 7.24/1.44  fof(f20,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.24/1.44    inference(ennf_transformation,[],[f5])).
% 7.24/1.44  
% 7.24/1.44  fof(f21,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.24/1.44    inference(flattening,[],[f20])).
% 7.24/1.44  
% 7.24/1.44  fof(f57,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f21])).
% 7.24/1.44  
% 7.24/1.44  fof(f1,axiom,(
% 7.24/1.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.24/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.44  
% 7.24/1.44  fof(f12,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.24/1.44    inference(ennf_transformation,[],[f1])).
% 7.24/1.44  
% 7.24/1.44  fof(f13,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.24/1.44    inference(flattening,[],[f12])).
% 7.24/1.44  
% 7.24/1.44  fof(f29,plain,(
% 7.24/1.44    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.24/1.44    inference(nnf_transformation,[],[f13])).
% 7.24/1.44  
% 7.24/1.44  fof(f45,plain,(
% 7.24/1.44    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f29])).
% 7.24/1.44  
% 7.24/1.44  fof(f63,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f37])).
% 7.24/1.44  
% 7.24/1.44  fof(f55,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f21])).
% 7.24/1.44  
% 7.24/1.44  fof(f64,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f37])).
% 7.24/1.44  
% 7.24/1.44  fof(f56,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f21])).
% 7.24/1.44  
% 7.24/1.44  fof(f48,plain,(
% 7.24/1.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f31])).
% 7.24/1.44  
% 7.24/1.44  fof(f95,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.24/1.44    inference(equality_resolution,[],[f48])).
% 7.24/1.44  
% 7.24/1.44  fof(f71,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 7.24/1.44    inference(cnf_transformation,[],[f37])).
% 7.24/1.44  
% 7.24/1.44  fof(f61,plain,(
% 7.24/1.44    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.24/1.44    inference(cnf_transformation,[],[f34])).
% 7.24/1.44  
% 7.24/1.44  fof(f89,plain,(
% 7.24/1.44    v5_pre_topc(sK7,sK5,sK3)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f93,plain,(
% 7.24/1.44    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  fof(f85,plain,(
% 7.24/1.44    v5_pre_topc(sK6,sK4,sK3)),
% 7.24/1.44    inference(cnf_transformation,[],[f44])).
% 7.24/1.44  
% 7.24/1.44  cnf(c_30,negated_conjecture,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f91]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1311,negated_conjecture,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_30]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2048,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_4,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
% 7.24/1.44      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
% 7.24/1.44      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
% 7.24/1.44      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(X2,X1,X0,X3,X4,X5),u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_pre_topc(X3,X2)
% 7.24/1.44      | ~ m1_pre_topc(X0,X2)
% 7.24/1.44      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.24/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(X2,X1,X0,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | v2_struct_0(X0)
% 7.24/1.44      | v2_struct_0(X3)
% 7.24/1.44      | ~ v1_funct_1(X5)
% 7.24/1.44      | ~ v1_funct_1(X4)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(X2,X1,X0,X3,X4,X5)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f96]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1321,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53)
% 7.24/1.44      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53))
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X3_54,X2_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X2_54)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X2_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X2_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(X2_54)
% 7.24/1.44      | v2_struct_0(X3_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_4]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2038,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53) = iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_7,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.24/1.44      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.24/1.44      | ~ m1_pre_topc(X1,X5)
% 7.24/1.44      | ~ m1_pre_topc(X4,X5)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.24/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ v2_pre_topc(X5)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X5)
% 7.24/1.44      | v2_struct_0(X5)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | v2_struct_0(X4)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | ~ v1_funct_1(X3)
% 7.24/1.44      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f50]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1318,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X2_54,X3_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X3_54)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X3_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X3_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(X2_54)
% 7.24/1.44      | v2_struct_0(X3_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_7]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2041,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.24/1.44      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.24/1.44      | ~ m1_pre_topc(X1,X5)
% 7.24/1.44      | ~ m1_pre_topc(X4,X5)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.24/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.24/1.44      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ v2_pre_topc(X5)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X5)
% 7.24/1.44      | v2_struct_0(X5)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | v2_struct_0(X4)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | ~ v1_funct_1(X3) ),
% 7.24/1.44      inference(cnf_transformation,[],[f52]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1320,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X2_54,X3_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X3_54)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.24/1.44      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X3_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X3_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(X2_54)
% 7.24/1.44      | v2_struct_0(X3_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_5]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2039,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)))) = iProver_top
% 7.24/1.44      | v2_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_6,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.24/1.44      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.24/1.44      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 7.24/1.44      | ~ m1_pre_topc(X1,X5)
% 7.24/1.44      | ~ m1_pre_topc(X4,X5)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.24/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ v2_pre_topc(X5)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X5)
% 7.24/1.44      | v2_struct_0(X5)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | v2_struct_0(X4)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | ~ v1_funct_1(X3) ),
% 7.24/1.44      inference(cnf_transformation,[],[f51]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1319,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.24/1.44      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X2_54,X3_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X3_54)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X3_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X3_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(X2_54)
% 7.24/1.44      | v2_struct_0(X3_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_6]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2040,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)) = iProver_top
% 7.24/1.44      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2567,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53) = iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top ),
% 7.24/1.44      inference(forward_subsumption_resolution,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_2038,c_2041,c_2039,c_2040]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12333,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_2048,c_2567]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_48,negated_conjecture,
% 7.24/1.44      ( ~ v2_struct_0(sK2) ),
% 7.24/1.44      inference(cnf_transformation,[],[f73]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_49,plain,
% 7.24/1.44      ( v2_struct_0(sK2) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_47,negated_conjecture,
% 7.24/1.44      ( v2_pre_topc(sK2) ),
% 7.24/1.44      inference(cnf_transformation,[],[f74]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_50,plain,
% 7.24/1.44      ( v2_pre_topc(sK2) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_46,negated_conjecture,
% 7.24/1.44      ( l1_pre_topc(sK2) ),
% 7.24/1.44      inference(cnf_transformation,[],[f75]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_51,plain,
% 7.24/1.44      ( l1_pre_topc(sK2) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_45,negated_conjecture,
% 7.24/1.44      ( ~ v2_struct_0(sK3) ),
% 7.24/1.44      inference(cnf_transformation,[],[f76]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_52,plain,
% 7.24/1.44      ( v2_struct_0(sK3) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_44,negated_conjecture,
% 7.24/1.44      ( v2_pre_topc(sK3) ),
% 7.24/1.44      inference(cnf_transformation,[],[f77]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_53,plain,
% 7.24/1.44      ( v2_pre_topc(sK3) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_43,negated_conjecture,
% 7.24/1.44      ( l1_pre_topc(sK3) ),
% 7.24/1.44      inference(cnf_transformation,[],[f78]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_54,plain,
% 7.24/1.44      ( l1_pre_topc(sK3) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_42,negated_conjecture,
% 7.24/1.44      ( ~ v2_struct_0(sK4) ),
% 7.24/1.44      inference(cnf_transformation,[],[f79]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_55,plain,
% 7.24/1.44      ( v2_struct_0(sK4) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_41,negated_conjecture,
% 7.24/1.44      ( m1_pre_topc(sK4,sK2) ),
% 7.24/1.44      inference(cnf_transformation,[],[f80]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_56,plain,
% 7.24/1.44      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_40,negated_conjecture,
% 7.24/1.44      ( ~ v2_struct_0(sK5) ),
% 7.24/1.44      inference(cnf_transformation,[],[f81]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_57,plain,
% 7.24/1.44      ( v2_struct_0(sK5) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_39,negated_conjecture,
% 7.24/1.44      ( m1_pre_topc(sK5,sK2) ),
% 7.24/1.44      inference(cnf_transformation,[],[f82]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_58,plain,
% 7.24/1.44      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_38,negated_conjecture,
% 7.24/1.44      ( v1_funct_1(sK6) ),
% 7.24/1.44      inference(cnf_transformation,[],[f83]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_59,plain,
% 7.24/1.44      ( v1_funct_1(sK6) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_37,negated_conjecture,
% 7.24/1.44      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f84]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_60,plain,
% 7.24/1.44      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_35,negated_conjecture,
% 7.24/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 7.24/1.44      inference(cnf_transformation,[],[f86]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_62,plain,
% 7.24/1.44      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_34,negated_conjecture,
% 7.24/1.44      ( v1_funct_1(sK7) ),
% 7.24/1.44      inference(cnf_transformation,[],[f87]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_63,plain,
% 7.24/1.44      ( v1_funct_1(sK7) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_33,negated_conjecture,
% 7.24/1.44      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f88]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_64,plain,
% 7.24/1.44      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_31,negated_conjecture,
% 7.24/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.24/1.44      inference(cnf_transformation,[],[f90]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_66,plain,
% 7.24/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_67,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2834,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X1_53,X0_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1318]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3601,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_53,X0_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2834]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5007,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.24/1.44      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.24/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.24/1.44      | ~ v2_pre_topc(sK3)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(sK3)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK3)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7))
% 7.24/1.44      | ~ v1_funct_1(sK7) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_3601]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5008,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)) = iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_5007]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5010,plain,
% 7.24/1.44      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_5008]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2844,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X1_54))
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,X1_54,sK4,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1319]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3761,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_53,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2844]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5052,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 7.24/1.44      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.24/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.24/1.44      | ~ v2_pre_topc(sK3)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(sK3)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK3)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(sK7) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_3761]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5053,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_5052]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5055,plain,
% 7.24/1.44      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_5053]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2854,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1320]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3821,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2854]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5185,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.24/1.44      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 7.24/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.24/1.44      | ~ v2_pre_topc(sK3)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(sK3)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK3)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(sK7) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_3821]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5186,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_5185]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5188,plain,
% 7.24/1.44      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_5186]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2869,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,k1_tsep_1(sK2,X0_54,sK5),X0_54,k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53)),X0_53)
% 7.24/1.44      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,X0_54,k2_tsep_1(sK2,X0_54,sK5),X0_53),k3_tmap_1(sK2,X1_54,sK5,k2_tsep_1(sK2,X0_54,sK5),X1_53))
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK5),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(sK2,X1_54,X0_54,sK5,X0_53,X1_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1321]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3922,plain,
% 7.24/1.44      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,X0_54,sK5,k2_tsep_1(sK2,sK4,sK5),X1_53))
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)),X0_53)
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2869]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5278,plain,
% 7.24/1.44      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),X0_53)
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 7.24/1.44      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 7.24/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.24/1.44      | ~ v2_pre_topc(sK3)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(sK3)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK3)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7))
% 7.24/1.44      | ~ v1_funct_1(sK7) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_3922]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5279,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),X0_53) = iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)) != iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_5278]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5281,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_5279]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12391,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_12333,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 7.24/1.44                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_5010,c_5055,
% 7.24/1.44                 c_5188,c_5281]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_23,plain,
% 7.24/1.44      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.24/1.44      | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
% 7.24/1.44      inference(cnf_transformation,[],[f66]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_17,plain,
% 7.24/1.44      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.24/1.44      | sP0(X4,X3,X2,X1,X0)
% 7.24/1.44      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
% 7.24/1.44      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 7.24/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 7.24/1.44      | ~ v1_funct_1(X2) ),
% 7.24/1.44      inference(cnf_transformation,[],[f58]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_27,plain,
% 7.24/1.44      ( sP1(X0,X1,X2,X3,X4)
% 7.24/1.44      | ~ r4_tsep_1(X0,X1,X3)
% 7.24/1.44      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 7.24/1.44      | ~ m1_pre_topc(X3,X0)
% 7.24/1.44      | ~ m1_pre_topc(X1,X0)
% 7.24/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 7.24/1.44      | ~ v2_pre_topc(X4)
% 7.24/1.44      | ~ v2_pre_topc(X0)
% 7.24/1.44      | ~ l1_pre_topc(X4)
% 7.24/1.44      | ~ l1_pre_topc(X0)
% 7.24/1.44      | v2_struct_0(X0)
% 7.24/1.44      | v2_struct_0(X4)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | v2_struct_0(X3)
% 7.24/1.44      | ~ v1_funct_1(X2) ),
% 7.24/1.44      inference(cnf_transformation,[],[f72]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_29,negated_conjecture,
% 7.24/1.44      ( r4_tsep_1(sK2,sK4,sK5) ),
% 7.24/1.44      inference(cnf_transformation,[],[f92]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_515,plain,
% 7.24/1.44      ( sP1(X0,X1,X2,X3,X4)
% 7.24/1.44      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 7.24/1.44      | ~ m1_pre_topc(X3,X0)
% 7.24/1.44      | ~ m1_pre_topc(X1,X0)
% 7.24/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 7.24/1.44      | ~ v2_pre_topc(X0)
% 7.24/1.44      | ~ v2_pre_topc(X4)
% 7.24/1.44      | ~ l1_pre_topc(X0)
% 7.24/1.44      | ~ l1_pre_topc(X4)
% 7.24/1.44      | v2_struct_0(X0)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | v2_struct_0(X3)
% 7.24/1.44      | v2_struct_0(X4)
% 7.24/1.44      | ~ v1_funct_1(X2)
% 7.24/1.44      | sK5 != X3
% 7.24/1.44      | sK4 != X1
% 7.24/1.44      | sK2 != X0 ),
% 7.24/1.44      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_516,plain,
% 7.24/1.44      ( sP1(sK2,sK4,X0,sK5,X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0) ),
% 7.24/1.44      inference(unflattening,[status(thm)],[c_515]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_520,plain,
% 7.24/1.44      ( v2_struct_0(X1)
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | sP1(sK2,sK4,X0,sK5,X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | ~ v1_funct_1(X0) ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_516,c_48,c_47,c_46,c_42,c_41,c_40,c_39]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_521,plain,
% 7.24/1.44      ( sP1(sK2,sK4,X0,sK5,X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0) ),
% 7.24/1.44      inference(renaming,[status(thm)],[c_520]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_556,plain,
% 7.24/1.44      ( sP0(X0,X1,X2,X3,X4)
% 7.24/1.44      | ~ v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
% 7.24/1.44      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X4,X3,X1)),u1_struct_0(X0))
% 7.24/1.44      | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
% 7.24/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X4,X3,X1)),u1_struct_0(X0))))
% 7.24/1.44      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
% 7.24/1.44      | ~ v2_pre_topc(X6)
% 7.24/1.44      | ~ l1_pre_topc(X6)
% 7.24/1.44      | v2_struct_0(X6)
% 7.24/1.44      | ~ v1_funct_1(X2)
% 7.24/1.44      | ~ v1_funct_1(X5)
% 7.24/1.44      | X5 != X2
% 7.24/1.44      | X6 != X0
% 7.24/1.44      | sK5 != X1
% 7.24/1.44      | sK4 != X3
% 7.24/1.44      | sK2 != X4 ),
% 7.24/1.44      inference(resolution_lifted,[status(thm)],[c_17,c_521]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_557,plain,
% 7.24/1.44      ( sP0(X0,sK5,X1,sK4,sK2)
% 7.24/1.44      | ~ v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
% 7.24/1.44      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
% 7.24/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
% 7.24/1.44      | ~ v2_pre_topc(X0)
% 7.24/1.44      | ~ l1_pre_topc(X0)
% 7.24/1.44      | v2_struct_0(X0)
% 7.24/1.44      | ~ v1_funct_1(X1) ),
% 7.24/1.44      inference(unflattening,[status(thm)],[c_556]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_790,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | X0 != X6
% 7.24/1.44      | X1 != X3
% 7.24/1.44      | sK5 != X5
% 7.24/1.44      | sK4 != X4
% 7.24/1.44      | sK2 != X2 ),
% 7.24/1.44      inference(resolution_lifted,[status(thm)],[c_23,c_557]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_791,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0) ),
% 7.24/1.44      inference(unflattening,[status(thm)],[c_790]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1288,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_791]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2071,plain,
% 7.24/1.44      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) = iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_8,plain,
% 7.24/1.44      ( ~ m1_pre_topc(X0,X1)
% 7.24/1.44      | ~ m1_pre_topc(X2,X1)
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | v2_struct_0(X0) ),
% 7.24/1.44      inference(cnf_transformation,[],[f54]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1317,plain,
% 7.24/1.44      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.24/1.44      | ~ m1_pre_topc(X2_54,X1_54)
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(X1_54,X2_54,X0_54),X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(X2_54) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_8]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2780,plain,
% 7.24/1.44      ( ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,X0_54,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK2) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1317]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2963,plain,
% 7.24/1.44      ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2780]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2964,plain,
% 7.24/1.44      ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_2963]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_10,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.24/1.44      | ~ m1_pre_topc(X3,X4)
% 7.24/1.44      | ~ m1_pre_topc(X1,X4)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ v2_pre_topc(X4)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X4)
% 7.24/1.44      | v2_struct_0(X4)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | ~ v1_funct_1(X0) ),
% 7.24/1.44      inference(cnf_transformation,[],[f57]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1315,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X2_54,X3_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X3_54)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X3_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X3_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X3_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_10]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2824,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X1_54,X0_54,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1315]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3447,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2824]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3448,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) = iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_3447]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_11136,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) = iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_2071,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,c_3448]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1,plain,
% 7.24/1.44      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.24/1.44      | ~ v1_funct_2(X3,X0,X1)
% 7.24/1.44      | ~ v1_funct_2(X2,X0,X1)
% 7.24/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.24/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.24/1.44      | ~ v1_funct_1(X3)
% 7.24/1.44      | ~ v1_funct_1(X2)
% 7.24/1.44      | X2 = X3 ),
% 7.24/1.44      inference(cnf_transformation,[],[f45]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1324,plain,
% 7.24/1.44      ( ~ r2_funct_2(X0_55,X1_55,X0_53,X1_53)
% 7.24/1.44      | ~ v1_funct_2(X1_53,X0_55,X1_55)
% 7.24/1.44      | ~ v1_funct_2(X0_53,X0_55,X1_55)
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | X0_53 = X1_53 ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_1]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2035,plain,
% 7.24/1.44      ( X0_53 = X1_53
% 7.24/1.44      | r2_funct_2(X0_55,X1_55,X0_53,X1_53) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,X0_55,X1_55) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,X0_55,X1_55) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_11151,plain,
% 7.24/1.44      ( k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53) = X1_53
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),X1_53) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_11136,c_2035]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_26,plain,
% 7.24/1.44      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f63]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_700,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
% 7.24/1.44      | X0 != X6
% 7.24/1.44      | X1 != X3
% 7.24/1.44      | sK5 != X5
% 7.24/1.44      | sK4 != X4
% 7.24/1.44      | sK2 != X2 ),
% 7.24/1.44      inference(resolution_lifted,[status(thm)],[c_26,c_557]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_701,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
% 7.24/1.44      inference(unflattening,[status(thm)],[c_700]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1291,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_701]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2068,plain,
% 7.24/1.44      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1291]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.24/1.44      | ~ m1_pre_topc(X3,X4)
% 7.24/1.44      | ~ m1_pre_topc(X1,X4)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ v2_pre_topc(X4)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X4)
% 7.24/1.44      | v2_struct_0(X4)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f55]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1313,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X2_54,X3_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X3_54)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X3_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X3_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X3_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_12]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2804,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X1_54,X0_54,sK4,X0_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1313]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3327,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2804]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3328,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_3327]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_10144,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) = iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_2068,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,c_3328]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_25,plain,
% 7.24/1.44      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.24/1.44      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f64]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_730,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | X0 != X6
% 7.24/1.44      | X1 != X3
% 7.24/1.44      | sK5 != X5
% 7.24/1.44      | sK4 != X4
% 7.24/1.44      | sK2 != X2 ),
% 7.24/1.44      inference(resolution_lifted,[status(thm)],[c_25,c_557]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_731,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0) ),
% 7.24/1.44      inference(unflattening,[status(thm)],[c_730]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1290,plain,
% 7.24/1.44      ( ~ v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_731]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2069,plain,
% 7.24/1.44      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1290]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_11,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.24/1.44      | ~ m1_pre_topc(X4,X3)
% 7.24/1.44      | ~ m1_pre_topc(X1,X3)
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ v2_pre_topc(X3)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X3)
% 7.24/1.44      | v2_struct_0(X3)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | ~ v1_funct_1(X0) ),
% 7.24/1.44      inference(cnf_transformation,[],[f56]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1314,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X3_54,X2_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X2_54)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X2_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X2_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X2_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_11]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2814,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X1_54,X0_54,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1314]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3387,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2814]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3388,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_3387]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_10742,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_2069,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,c_3388]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12505,plain,
% 7.24/1.44      ( v1_funct_1(X1_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53) = X1_53
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),X1_53) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_11151,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_2964,
% 7.24/1.44                 c_3328,c_3388]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12506,plain,
% 7.24/1.44      ( k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53) = X1_53
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),X1_53) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top ),
% 7.24/1.44      inference(renaming,[status(thm)],[c_12505]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12522,plain,
% 7.24/1.44      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_12391,c_12506]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2044,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 7.24/1.44      | v2_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_7033,plain,
% 7.24/1.44      ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
% 7.24/1.44      | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X3_54,X0_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53)) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_2044,c_2035]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2046,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X3_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2045,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
% 7.24/1.44      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1314]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_11019,plain,
% 7.24/1.44      ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
% 7.24/1.44      | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X3_54,X0_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top ),
% 7.24/1.44      inference(forward_subsumption_resolution,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_7033,c_2046,c_2045]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12396,plain,
% 7.24/1.44      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_12391,c_11019]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12622,plain,
% 7.24/1.44      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_12522,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 7.24/1.44                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_2964,c_5010,c_5055,
% 7.24/1.44                 c_5188,c_12396]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
% 7.24/1.44      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
% 7.24/1.44      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 7.24/1.44      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(X2,X1,X3,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_pre_topc(X0,X2)
% 7.24/1.44      | ~ m1_pre_topc(X3,X2)
% 7.24/1.44      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.24/1.44      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(X2,X1,X3,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ v2_pre_topc(X2)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X2)
% 7.24/1.44      | v2_struct_0(X2)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | v2_struct_0(X3)
% 7.24/1.44      | v2_struct_0(X0)
% 7.24/1.44      | ~ v1_funct_1(X5)
% 7.24/1.44      | ~ v1_funct_1(X4)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(X2,X1,X3,X0,X4,X5)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f95]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1322,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53)
% 7.24/1.44      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X3_54,X2_54)
% 7.24/1.44      | ~ m1_pre_topc(X0_54,X2_54)
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(X2_54)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(X2_54)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(X2_54)
% 7.24/1.44      | v2_struct_0(X3_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_3]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2037,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53) = iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2527,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53) = iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53)) != iProver_top
% 7.24/1.44      | v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 7.24/1.44      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.24/1.44      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X2_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X1_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X1_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X3_54) = iProver_top
% 7.24/1.44      | v2_struct_0(X2_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(X1_53) != iProver_top ),
% 7.24/1.44      inference(forward_subsumption_resolution,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_2037,c_2041,c_2039,c_2040]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_11684,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_2048,c_2527]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2884,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,k1_tsep_1(sK2,sK4,X0_54),X0_54,k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53)),X1_53)
% 7.24/1.44      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54),k3_tmap_1(sK2,X1_54,sK4,k2_tsep_1(sK2,sK4,X0_54),X0_53),k3_tmap_1(sK2,X1_54,X0_54,k2_tsep_1(sK2,sK4,X0_54),X1_53))
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(X1_54))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(sK2,X1_54,sK4,X0_54,X0_53,X1_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1322]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_4005,plain,
% 7.24/1.44      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,X0_54,sK5,k2_tsep_1(sK2,sK4,sK5),X1_53))
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_54),k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)),X1_53)
% 7.24/1.44      | ~ v1_funct_2(X1_53,u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(X1_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X0_53,X1_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2884]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5350,plain,
% 7.24/1.44      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),sK7)
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 7.24/1.44      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK4,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 7.24/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.24/1.44      | ~ v2_pre_topc(sK3)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(sK3)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(sK5)
% 7.24/1.44      | v2_struct_0(sK4)
% 7.24/1.44      | v2_struct_0(sK3)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7))
% 7.24/1.44      | ~ v1_funct_1(sK7) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_4005]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5351,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),sK7) = iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)) != iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_5350]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_5353,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 7.24/1.44      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK5) = iProver_top
% 7.24/1.44      | v2_struct_0(sK4) = iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top
% 7.24/1.44      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_5351]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_11972,plain,
% 7.24/1.44      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_11684,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 7.24/1.44                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_5010,c_5055,
% 7.24/1.44                 c_5188,c_5353]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_11978,plain,
% 7.24/1.44      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.24/1.44      | v1_funct_1(sK7) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_11972,c_11019]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12173,plain,
% 7.24/1.44      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_11978,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 7.24/1.44                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_2964,c_5010,c_5055,
% 7.24/1.44                 c_5188]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_18,plain,
% 7.24/1.44      ( sP0(X0,X1,X2,X3,X4)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f71]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_14,plain,
% 7.24/1.44      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.24/1.44      | ~ sP0(X4,X3,X2,X1,X0)
% 7.24/1.44      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 7.24/1.44      inference(cnf_transformation,[],[f61]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_590,plain,
% 7.24/1.44      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.24/1.44      | v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
% 7.24/1.44      | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
% 7.24/1.44      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
% 7.24/1.44      | ~ v2_pre_topc(X6)
% 7.24/1.44      | ~ l1_pre_topc(X6)
% 7.24/1.44      | v2_struct_0(X6)
% 7.24/1.44      | ~ v1_funct_1(X5)
% 7.24/1.44      | X5 != X2
% 7.24/1.44      | X6 != X0
% 7.24/1.44      | sK5 != X1
% 7.24/1.44      | sK4 != X3
% 7.24/1.44      | sK2 != X4 ),
% 7.24/1.44      inference(resolution_lifted,[status(thm)],[c_14,c_521]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_591,plain,
% 7.24/1.44      ( ~ sP0(X0,sK5,X1,sK4,sK2)
% 7.24/1.44      | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
% 7.24/1.44      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
% 7.24/1.44      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
% 7.24/1.44      | ~ v2_pre_topc(X0)
% 7.24/1.44      | ~ l1_pre_topc(X0)
% 7.24/1.44      | v2_struct_0(X0)
% 7.24/1.44      | ~ v1_funct_1(X1) ),
% 7.24/1.44      inference(unflattening,[status(thm)],[c_590]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_649,plain,
% 7.24/1.44      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),X5,X3)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),X4,X3)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6))
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
% 7.24/1.44      | X0 != X6
% 7.24/1.44      | X1 != X3
% 7.24/1.44      | sK5 != X5
% 7.24/1.44      | sK4 != X4
% 7.24/1.44      | sK2 != X2 ),
% 7.24/1.44      inference(resolution_lifted,[status(thm)],[c_18,c_591]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_650,plain,
% 7.24/1.44      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),sK5,X1)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),sK4,X1)
% 7.24/1.44      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
% 7.24/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 7.24/1.44      | ~ v2_pre_topc(X1)
% 7.24/1.44      | ~ l1_pre_topc(X1)
% 7.24/1.44      | v2_struct_0(X1)
% 7.24/1.44      | ~ v1_funct_1(X0)
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0))
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
% 7.24/1.44      inference(unflattening,[status(thm)],[c_649]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1292,plain,
% 7.24/1.44      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54)
% 7.24/1.44      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54)
% 7.24/1.44      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.24/1.44      | ~ v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53))
% 7.24/1.44      | ~ v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) ),
% 7.24/1.44      inference(subtyping,[status(esa)],[c_650]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2067,plain,
% 7.24/1.44      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
% 7.24/1.44      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
% 7.24/1.44      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1292]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_1396,plain,
% 7.24/1.44      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
% 7.24/1.44      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
% 7.24/1.44      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_1292]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2799,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X1_54,X0_54,sK5,X0_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1313]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3297,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53)
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2799]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3298,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top
% 7.24/1.44      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_3297]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2809,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X1_54,X0_54,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1314]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3357,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2809]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3358,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) = iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_3357]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_2819,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.24/1.44      | ~ m1_pre_topc(X0_54,sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X1_54,X0_54,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_54))))
% 7.24/1.44      | ~ v2_pre_topc(X1_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X1_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X1_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_1315]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3417,plain,
% 7.24/1.44      ( ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 7.24/1.44      | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 7.24/1.44      | ~ m1_pre_topc(sK5,sK2)
% 7.24/1.44      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 7.24/1.44      | ~ v2_pre_topc(X0_54)
% 7.24/1.44      | ~ v2_pre_topc(sK2)
% 7.24/1.44      | ~ l1_pre_topc(X0_54)
% 7.24/1.44      | ~ l1_pre_topc(sK2)
% 7.24/1.44      | v2_struct_0(X0_54)
% 7.24/1.44      | v2_struct_0(sK2)
% 7.24/1.44      | ~ v1_funct_1(X0_53) ),
% 7.24/1.44      inference(instantiation,[status(thm)],[c_2819]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_3418,plain,
% 7.24/1.44      ( v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 7.24/1.44      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) = iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK2) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK2) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v2_struct_0(sK2) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_3417]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_9664,plain,
% 7.24/1.44      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
% 7.24/1.44      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
% 7.24/1.44      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
% 7.24/1.44      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 7.24/1.44      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | l1_pre_topc(X0_54) != iProver_top
% 7.24/1.44      | v2_struct_0(X0_54) = iProver_top
% 7.24/1.44      | v1_funct_1(X0_53) != iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_2067,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_1396,c_2964,
% 7.24/1.44                 c_3298,c_3328,c_3358,c_3388,c_3418,c_3448]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12182,plain,
% 7.24/1.44      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 7.24/1.44      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 7.24/1.44      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v2_pre_topc(sK3) != iProver_top
% 7.24/1.44      | l1_pre_topc(sK3) != iProver_top
% 7.24/1.44      | v2_struct_0(sK3) = iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.24/1.44      inference(superposition,[status(thm)],[c_12173,c_9664]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_32,negated_conjecture,
% 7.24/1.44      ( v5_pre_topc(sK7,sK5,sK3) ),
% 7.24/1.44      inference(cnf_transformation,[],[f89]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_65,plain,
% 7.24/1.44      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_28,negated_conjecture,
% 7.24/1.44      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
% 7.24/1.44      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 7.24/1.44      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 7.24/1.44      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.24/1.44      inference(cnf_transformation,[],[f93]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_69,plain,
% 7.24/1.44      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
% 7.24/1.44      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.24/1.44      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.24/1.44      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12308,plain,
% 7.24/1.44      ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top ),
% 7.24/1.44      inference(global_propositional_subsumption,
% 7.24/1.44                [status(thm)],
% 7.24/1.44                [c_12182,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 7.24/1.44                 c_58,c_59,c_60,c_62,c_63,c_64,c_65,c_66,c_69,c_5010,
% 7.24/1.44                 c_5055,c_5188]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_12626,plain,
% 7.24/1.44      ( v5_pre_topc(sK6,sK4,sK3) != iProver_top ),
% 7.24/1.44      inference(demodulation,[status(thm)],[c_12622,c_12308]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_36,negated_conjecture,
% 7.24/1.44      ( v5_pre_topc(sK6,sK4,sK3) ),
% 7.24/1.44      inference(cnf_transformation,[],[f85]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(c_61,plain,
% 7.24/1.44      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 7.24/1.44      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.24/1.44  
% 7.24/1.44  cnf(contradiction,plain,
% 7.24/1.44      ( $false ),
% 7.24/1.44      inference(minisat,[status(thm)],[c_12626,c_61]) ).
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.24/1.44  
% 7.24/1.44  ------                               Statistics
% 7.24/1.44  
% 7.24/1.44  ------ General
% 7.24/1.44  
% 7.24/1.44  abstr_ref_over_cycles:                  0
% 7.24/1.44  abstr_ref_under_cycles:                 0
% 7.24/1.44  gc_basic_clause_elim:                   0
% 7.24/1.44  forced_gc_time:                         0
% 7.24/1.44  parsing_time:                           0.014
% 7.24/1.44  unif_index_cands_time:                  0.
% 7.24/1.44  unif_index_add_time:                    0.
% 7.24/1.44  orderings_time:                         0.
% 7.24/1.44  out_proof_time:                         0.03
% 7.24/1.44  total_time:                             0.754
% 7.24/1.44  num_of_symbols:                         58
% 7.24/1.44  num_of_terms:                           28138
% 7.24/1.44  
% 7.24/1.44  ------ Preprocessing
% 7.24/1.44  
% 7.24/1.44  num_of_splits:                          0
% 7.24/1.44  num_of_split_atoms:                     0
% 7.24/1.44  num_of_reused_defs:                     0
% 7.24/1.44  num_eq_ax_congr_red:                    40
% 7.24/1.44  num_of_sem_filtered_clauses:            1
% 7.24/1.44  num_of_subtypes:                        5
% 7.24/1.44  monotx_restored_types:                  0
% 7.24/1.44  sat_num_of_epr_types:                   0
% 7.24/1.44  sat_num_of_non_cyclic_types:            0
% 7.24/1.44  sat_guarded_non_collapsed_types:        1
% 7.24/1.44  num_pure_diseq_elim:                    0
% 7.24/1.44  simp_replaced_by:                       0
% 7.24/1.44  res_preprocessed:                       194
% 7.24/1.44  prep_upred:                             0
% 7.24/1.44  prep_unflattend:                        73
% 7.24/1.44  smt_new_axioms:                         0
% 7.24/1.44  pred_elim_cands:                        9
% 7.24/1.44  pred_elim:                              3
% 7.24/1.44  pred_elim_cl:                           7
% 7.24/1.44  pred_elim_cycles:                       5
% 7.24/1.44  merged_defs:                            0
% 7.24/1.44  merged_defs_ncl:                        0
% 7.24/1.44  bin_hyper_res:                          0
% 7.24/1.44  prep_cycles:                            4
% 7.24/1.44  pred_elim_time:                         0.022
% 7.24/1.44  splitting_time:                         0.
% 7.24/1.44  sem_filter_time:                        0.
% 7.24/1.44  monotx_time:                            0.
% 7.24/1.44  subtype_inf_time:                       0.001
% 7.24/1.44  
% 7.24/1.44  ------ Problem properties
% 7.24/1.44  
% 7.24/1.44  clauses:                                42
% 7.24/1.44  conjectures:                            20
% 7.24/1.44  epr:                                    14
% 7.24/1.44  horn:                                   22
% 7.24/1.44  ground:                                 20
% 7.24/1.44  unary:                                  19
% 7.24/1.44  binary:                                 0
% 7.24/1.44  lits:                                   280
% 7.24/1.44  lits_eq:                                2
% 7.24/1.44  fd_pure:                                0
% 7.24/1.44  fd_pseudo:                              0
% 7.24/1.44  fd_cond:                                0
% 7.24/1.44  fd_pseudo_cond:                         2
% 7.24/1.44  ac_symbols:                             0
% 7.24/1.44  
% 7.24/1.44  ------ Propositional Solver
% 7.24/1.44  
% 7.24/1.44  prop_solver_calls:                      28
% 7.24/1.44  prop_fast_solver_calls:                 3813
% 7.24/1.44  smt_solver_calls:                       0
% 7.24/1.44  smt_fast_solver_calls:                  0
% 7.24/1.44  prop_num_of_clauses:                    5093
% 7.24/1.44  prop_preprocess_simplified:             12436
% 7.24/1.44  prop_fo_subsumed:                       245
% 7.24/1.44  prop_solver_time:                       0.
% 7.24/1.44  smt_solver_time:                        0.
% 7.24/1.44  smt_fast_solver_time:                   0.
% 7.24/1.44  prop_fast_solver_time:                  0.
% 7.24/1.44  prop_unsat_core_time:                   0.001
% 7.24/1.44  
% 7.24/1.44  ------ QBF
% 7.24/1.44  
% 7.24/1.44  qbf_q_res:                              0
% 7.24/1.44  qbf_num_tautologies:                    0
% 7.24/1.44  qbf_prep_cycles:                        0
% 7.24/1.44  
% 7.24/1.44  ------ BMC1
% 7.24/1.44  
% 7.24/1.44  bmc1_current_bound:                     -1
% 7.24/1.44  bmc1_last_solved_bound:                 -1
% 7.24/1.44  bmc1_unsat_core_size:                   -1
% 7.24/1.44  bmc1_unsat_core_parents_size:           -1
% 7.24/1.44  bmc1_merge_next_fun:                    0
% 7.24/1.44  bmc1_unsat_core_clauses_time:           0.
% 7.24/1.44  
% 7.24/1.44  ------ Instantiation
% 7.24/1.44  
% 7.24/1.44  inst_num_of_clauses:                    1263
% 7.24/1.44  inst_num_in_passive:                    472
% 7.24/1.44  inst_num_in_active:                     425
% 7.24/1.44  inst_num_in_unprocessed:                366
% 7.24/1.44  inst_num_of_loops:                      450
% 7.24/1.44  inst_num_of_learning_restarts:          0
% 7.24/1.44  inst_num_moves_active_passive:          24
% 7.24/1.44  inst_lit_activity:                      0
% 7.24/1.44  inst_lit_activity_moves:                1
% 7.24/1.44  inst_num_tautologies:                   0
% 7.24/1.44  inst_num_prop_implied:                  0
% 7.24/1.44  inst_num_existing_simplified:           0
% 7.24/1.44  inst_num_eq_res_simplified:             0
% 7.24/1.44  inst_num_child_elim:                    0
% 7.24/1.44  inst_num_of_dismatching_blockings:      447
% 7.24/1.44  inst_num_of_non_proper_insts:           642
% 7.24/1.44  inst_num_of_duplicates:                 0
% 7.24/1.44  inst_inst_num_from_inst_to_res:         0
% 7.24/1.44  inst_dismatching_checking_time:         0.
% 7.24/1.44  
% 7.24/1.44  ------ Resolution
% 7.24/1.44  
% 7.24/1.44  res_num_of_clauses:                     0
% 7.24/1.44  res_num_in_passive:                     0
% 7.24/1.44  res_num_in_active:                      0
% 7.24/1.44  res_num_of_loops:                       198
% 7.24/1.44  res_forward_subset_subsumed:            5
% 7.24/1.44  res_backward_subset_subsumed:           0
% 7.24/1.44  res_forward_subsumed:                   0
% 7.24/1.44  res_backward_subsumed:                  0
% 7.24/1.44  res_forward_subsumption_resolution:     0
% 7.24/1.44  res_backward_subsumption_resolution:    0
% 7.24/1.44  res_clause_to_clause_subsumption:       767
% 7.24/1.44  res_orphan_elimination:                 0
% 7.24/1.44  res_tautology_del:                      22
% 7.24/1.44  res_num_eq_res_simplified:              0
% 7.24/1.44  res_num_sel_changes:                    0
% 7.24/1.44  res_moves_from_active_to_pass:          0
% 7.24/1.44  
% 7.24/1.44  ------ Superposition
% 7.24/1.44  
% 7.24/1.44  sup_time_total:                         0.
% 7.24/1.44  sup_time_generating:                    0.
% 7.24/1.44  sup_time_sim_full:                      0.
% 7.24/1.44  sup_time_sim_immed:                     0.
% 7.24/1.44  
% 7.24/1.44  sup_num_of_clauses:                     101
% 7.24/1.44  sup_num_in_active:                      83
% 7.24/1.44  sup_num_in_passive:                     18
% 7.24/1.44  sup_num_of_loops:                       88
% 7.24/1.44  sup_fw_superposition:                   40
% 7.24/1.44  sup_bw_superposition:                   52
% 7.24/1.44  sup_immediate_simplified:               18
% 7.24/1.44  sup_given_eliminated:                   0
% 7.24/1.44  comparisons_done:                       0
% 7.24/1.44  comparisons_avoided:                    0
% 7.24/1.44  
% 7.24/1.44  ------ Simplifications
% 7.24/1.44  
% 7.24/1.44  
% 7.24/1.44  sim_fw_subset_subsumed:                 10
% 7.24/1.44  sim_bw_subset_subsumed:                 3
% 7.24/1.44  sim_fw_subsumed:                        8
% 7.24/1.44  sim_bw_subsumed:                        0
% 7.24/1.44  sim_fw_subsumption_res:                 17
% 7.24/1.44  sim_bw_subsumption_res:                 0
% 7.24/1.44  sim_tautology_del:                      1
% 7.24/1.44  sim_eq_tautology_del:                   7
% 7.24/1.44  sim_eq_res_simp:                        0
% 7.24/1.44  sim_fw_demodulated:                     2
% 7.24/1.44  sim_bw_demodulated:                     3
% 7.24/1.44  sim_light_normalised:                   4
% 7.24/1.44  sim_joinable_taut:                      0
% 7.24/1.44  sim_joinable_simp:                      0
% 7.24/1.44  sim_ac_normalised:                      0
% 7.24/1.44  sim_smt_subsumption:                    0
% 7.24/1.44  
%------------------------------------------------------------------------------
