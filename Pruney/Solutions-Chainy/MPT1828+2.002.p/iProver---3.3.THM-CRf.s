%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:24 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :  222 (2993 expanded)
%              Number of clauses        :  140 ( 632 expanded)
%              Number of leaves         :   16 (1189 expanded)
%              Depth                    :   25
%              Number of atoms          : 2474 (66247 expanded)
%              Number of equality atoms :  621 (1742 expanded)
%              Maximal formula depth    :   30 (  11 average)
%              Maximal clause size      :   48 (  10 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

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
    inference(pure_predicate_removal,[],[f9])).

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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f44,f43,f42,f41,f40,f39])).

fof(f92,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f48])).

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

fof(f51,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f19])).

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

fof(f30,plain,(
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

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f28,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(nnf_transformation,[],[f28])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f29,plain,(
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
    inference(definition_folding,[],[f21,f28,f27])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f49])).

fof(f86,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(k1_tsep_1(X1,X3,X0),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1316,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X3_54,X1_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | m1_pre_topc(k1_tsep_1(X1_54,X3_54,X0_54),X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2049,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X3_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_54,X3_54,X0_54),X2_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_30,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1313,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2052,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

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
    inference(cnf_transformation,[],[f97])).

cnf(c_1323,plain,
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
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2042,plain,
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
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

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
    inference(cnf_transformation,[],[f51])).

cnf(c_1320,plain,
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
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2045,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

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
    inference(cnf_transformation,[],[f53])).

cnf(c_1322,plain,
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
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2043,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

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
    inference(cnf_transformation,[],[f52])).

cnf(c_1321,plain,
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
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2044,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_2571,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2042,c_2045,c_2043,c_2044])).

cnf(c_9492,plain,
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
    inference(superposition,[status(thm)],[c_2052,c_2571])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_52,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_53,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_54,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_55,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_56,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_57,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_58,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_59,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_60,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_62,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_63,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_64,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_66,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_67,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2813,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(sK5,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_53,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_3055,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2813])).

cnf(c_3575,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
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
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3055])).

cnf(c_3576,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3575])).

cnf(c_2823,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(sK5,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_3073,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2823])).

cnf(c_3584,plain,
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
    inference(instantiation,[status(thm)],[c_3073])).

cnf(c_3586,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3584])).

cnf(c_3588,plain,
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
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_2833,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(sK5,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_3087,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2833])).

cnf(c_3748,plain,
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
    inference(instantiation,[status(thm)],[c_3087])).

cnf(c_3749,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3748])).

cnf(c_3751,plain,
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
    inference(instantiation,[status(thm)],[c_3749])).

cnf(c_2858,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_54,sK4,X1_54)),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,sK4,k2_tsep_1(X0_54,sK4,X1_54),sK6),k3_tmap_1(X0_54,sK3,X1_54,k2_tsep_1(X0_54,sK4,X1_54),X0_53))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,k1_tsep_1(X0_54,sK4,X1_54),sK4,k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53)),sK6)
    | ~ v1_funct_2(X0_53,u1_struct_0(X1_54),u1_struct_0(sK3))
    | ~ v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53),u1_struct_0(k1_tsep_1(X0_54,sK4,X1_54)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ m1_pre_topc(sK4,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,X1_54)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_3108,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X0_54)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X0_54),sK6),k3_tmap_1(sK2,sK3,X0_54,k2_tsep_1(sK2,sK4,X0_54),X0_53))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X0_54),sK4,k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53)),sK6)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_3897,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X0_53))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53)),sK6)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_6820,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
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
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3897])).

cnf(c_6821,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_6820])).

cnf(c_9530,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9492,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_3576,c_3588,c_3751,c_6821])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_1319,plain,
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
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2046,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1326,plain,
    ( ~ r2_funct_2(X0_55,X1_55,X0_53,X1_53)
    | ~ v1_funct_2(X1_53,X0_55,X1_55)
    | ~ v1_funct_2(X0_53,X0_55,X1_55)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | X0_53 = X1_53 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2039,plain,
    ( X0_53 = X1_53
    | r2_funct_2(X0_55,X1_55,X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_53,X0_55,X1_55) != iProver_top
    | v1_funct_2(X1_53,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_4280,plain,
    ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
    | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_2039])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_1317,plain,
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
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2048,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_1318,plain,
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
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2047,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_7546,plain,
    ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
    | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4280,c_2048,c_2047])).

cnf(c_9535,plain,
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
    inference(superposition,[status(thm)],[c_9530,c_7546])).

cnf(c_9730,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9535,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_3576,c_3588,c_3751])).

cnf(c_9731,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9730])).

cnf(c_9736,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_9731])).

cnf(c_27,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1315,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3726,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_3731,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3726])).

cnf(c_9788,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9736,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_3731])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_516,plain,
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
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_517,plain,
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
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_521,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | sP1(sK2,sK4,X0,sK5,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_48,c_47,c_46,c_42,c_41,c_40,c_39])).

cnf(c_522,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_521])).

cnf(c_591,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_522])).

cnf(c_592,plain,
    ( ~ sP0(X0,sK5,X1,sK4,sK2)
    | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_650,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_592])).

cnf(c_651,plain,
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
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_1294,plain,
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
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_2071,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_5867,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_2071])).

cnf(c_10011,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5867,c_49,c_50,c_51,c_58])).

cnf(c_10012,plain,
    ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10011])).

cnf(c_10034,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9788,c_10012])).

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
    inference(cnf_transformation,[],[f96])).

cnf(c_1324,plain,
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
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2041,plain,
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
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_2531,plain,
    ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53) = iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2041,c_2045,c_2043,c_2044])).

cnf(c_8634,plain,
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
    inference(superposition,[status(thm)],[c_2052,c_2531])).

cnf(c_2863,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_54,X1_54,sK5)),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,k2_tsep_1(X0_54,X1_54,sK5),X0_53),k3_tmap_1(X0_54,sK3,sK5,k2_tsep_1(X0_54,X1_54,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,k1_tsep_1(X0_54,X1_54,sK5),sK5,k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7)),sK7)
    | ~ v1_funct_2(X0_53,u1_struct_0(X1_54),u1_struct_0(sK3))
    | ~ v1_funct_2(k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(X0_54,X1_54,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ m1_pre_topc(sK5,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_3115,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X0_54,k2_tsep_1(sK2,X0_54,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,X0_54,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0_54,sK5),sK5,k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7)),sK7)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2863])).

cnf(c_3916,plain,
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
    inference(instantiation,[status(thm)],[c_3115])).

cnf(c_3917,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3916])).

cnf(c_3919,plain,
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
    inference(instantiation,[status(thm)],[c_3917])).

cnf(c_8819,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8634,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_3576,c_3588,c_3751,c_3919])).

cnf(c_8825,plain,
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
    inference(superposition,[status(thm)],[c_8819,c_7546])).

cnf(c_9000,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8825,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_3576,c_3588,c_3751])).

cnf(c_9001,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9000])).

cnf(c_9006,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_9001])).

cnf(c_9088,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9006,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_3731])).

cnf(c_10050,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10034,c_9088,c_9788])).

cnf(c_36,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_61,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_65,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_69,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10107,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10050,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_69,c_3576,c_3588,c_3751])).

cnf(c_10112,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_10107])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10112,c_3731,c_58,c_57,c_56,c_55,c_51,c_50,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:31:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 4.24/1.09  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.09  
% 4.24/1.09  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.24/1.09  
% 4.24/1.09  ------  iProver source info
% 4.24/1.09  
% 4.24/1.09  git: date: 2020-06-30 10:37:57 +0100
% 4.24/1.09  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.24/1.09  git: non_committed_changes: false
% 4.24/1.09  git: last_make_outside_of_git: false
% 4.24/1.09  
% 4.24/1.09  ------ 
% 4.24/1.09  
% 4.24/1.09  ------ Input Options
% 4.24/1.09  
% 4.24/1.09  --out_options                           all
% 4.24/1.09  --tptp_safe_out                         true
% 4.24/1.09  --problem_path                          ""
% 4.24/1.09  --include_path                          ""
% 4.24/1.09  --clausifier                            res/vclausify_rel
% 4.24/1.09  --clausifier_options                    --mode clausify
% 4.24/1.09  --stdin                                 false
% 4.24/1.09  --stats_out                             all
% 4.24/1.09  
% 4.24/1.09  ------ General Options
% 4.24/1.09  
% 4.24/1.09  --fof                                   false
% 4.24/1.09  --time_out_real                         305.
% 4.24/1.09  --time_out_virtual                      -1.
% 4.24/1.09  --symbol_type_check                     false
% 4.24/1.09  --clausify_out                          false
% 4.24/1.09  --sig_cnt_out                           false
% 4.24/1.09  --trig_cnt_out                          false
% 4.24/1.09  --trig_cnt_out_tolerance                1.
% 4.24/1.09  --trig_cnt_out_sk_spl                   false
% 4.24/1.09  --abstr_cl_out                          false
% 4.24/1.09  
% 4.24/1.09  ------ Global Options
% 4.24/1.09  
% 4.24/1.09  --schedule                              default
% 4.24/1.09  --add_important_lit                     false
% 4.24/1.09  --prop_solver_per_cl                    1000
% 4.24/1.09  --min_unsat_core                        false
% 4.24/1.09  --soft_assumptions                      false
% 4.24/1.09  --soft_lemma_size                       3
% 4.24/1.09  --prop_impl_unit_size                   0
% 4.24/1.09  --prop_impl_unit                        []
% 4.24/1.09  --share_sel_clauses                     true
% 4.24/1.09  --reset_solvers                         false
% 4.24/1.09  --bc_imp_inh                            [conj_cone]
% 4.24/1.09  --conj_cone_tolerance                   3.
% 4.24/1.09  --extra_neg_conj                        none
% 4.24/1.09  --large_theory_mode                     true
% 4.24/1.09  --prolific_symb_bound                   200
% 4.24/1.09  --lt_threshold                          2000
% 4.24/1.09  --clause_weak_htbl                      true
% 4.24/1.09  --gc_record_bc_elim                     false
% 4.24/1.09  
% 4.24/1.09  ------ Preprocessing Options
% 4.24/1.09  
% 4.24/1.09  --preprocessing_flag                    true
% 4.24/1.09  --time_out_prep_mult                    0.1
% 4.24/1.09  --splitting_mode                        input
% 4.24/1.09  --splitting_grd                         true
% 4.24/1.09  --splitting_cvd                         false
% 4.24/1.09  --splitting_cvd_svl                     false
% 4.24/1.09  --splitting_nvd                         32
% 4.24/1.09  --sub_typing                            true
% 4.24/1.09  --prep_gs_sim                           true
% 4.24/1.09  --prep_unflatten                        true
% 4.24/1.09  --prep_res_sim                          true
% 4.24/1.09  --prep_upred                            true
% 4.24/1.09  --prep_sem_filter                       exhaustive
% 4.24/1.09  --prep_sem_filter_out                   false
% 4.24/1.09  --pred_elim                             true
% 4.24/1.09  --res_sim_input                         true
% 4.24/1.09  --eq_ax_congr_red                       true
% 4.24/1.09  --pure_diseq_elim                       true
% 4.24/1.09  --brand_transform                       false
% 4.24/1.09  --non_eq_to_eq                          false
% 4.24/1.09  --prep_def_merge                        true
% 4.24/1.09  --prep_def_merge_prop_impl              false
% 4.24/1.09  --prep_def_merge_mbd                    true
% 4.24/1.09  --prep_def_merge_tr_red                 false
% 4.24/1.09  --prep_def_merge_tr_cl                  false
% 4.24/1.09  --smt_preprocessing                     true
% 4.24/1.09  --smt_ac_axioms                         fast
% 4.24/1.09  --preprocessed_out                      false
% 4.24/1.09  --preprocessed_stats                    false
% 4.24/1.09  
% 4.24/1.09  ------ Abstraction refinement Options
% 4.24/1.09  
% 4.24/1.09  --abstr_ref                             []
% 4.24/1.09  --abstr_ref_prep                        false
% 4.24/1.09  --abstr_ref_until_sat                   false
% 4.24/1.09  --abstr_ref_sig_restrict                funpre
% 4.24/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 4.24/1.09  --abstr_ref_under                       []
% 4.24/1.09  
% 4.24/1.09  ------ SAT Options
% 4.24/1.09  
% 4.24/1.09  --sat_mode                              false
% 4.24/1.09  --sat_fm_restart_options                ""
% 4.24/1.09  --sat_gr_def                            false
% 4.24/1.09  --sat_epr_types                         true
% 4.24/1.09  --sat_non_cyclic_types                  false
% 4.24/1.09  --sat_finite_models                     false
% 4.24/1.09  --sat_fm_lemmas                         false
% 4.24/1.09  --sat_fm_prep                           false
% 4.24/1.09  --sat_fm_uc_incr                        true
% 4.24/1.09  --sat_out_model                         small
% 4.24/1.09  --sat_out_clauses                       false
% 4.24/1.09  
% 4.24/1.09  ------ QBF Options
% 4.24/1.09  
% 4.24/1.09  --qbf_mode                              false
% 4.24/1.09  --qbf_elim_univ                         false
% 4.24/1.09  --qbf_dom_inst                          none
% 4.24/1.09  --qbf_dom_pre_inst                      false
% 4.24/1.09  --qbf_sk_in                             false
% 4.24/1.09  --qbf_pred_elim                         true
% 4.24/1.09  --qbf_split                             512
% 4.24/1.09  
% 4.24/1.09  ------ BMC1 Options
% 4.24/1.09  
% 4.24/1.09  --bmc1_incremental                      false
% 4.24/1.09  --bmc1_axioms                           reachable_all
% 4.24/1.09  --bmc1_min_bound                        0
% 4.24/1.09  --bmc1_max_bound                        -1
% 4.24/1.09  --bmc1_max_bound_default                -1
% 4.24/1.09  --bmc1_symbol_reachability              true
% 4.24/1.09  --bmc1_property_lemmas                  false
% 4.24/1.09  --bmc1_k_induction                      false
% 4.24/1.09  --bmc1_non_equiv_states                 false
% 4.24/1.09  --bmc1_deadlock                         false
% 4.24/1.09  --bmc1_ucm                              false
% 4.24/1.09  --bmc1_add_unsat_core                   none
% 4.24/1.09  --bmc1_unsat_core_children              false
% 4.24/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 4.24/1.09  --bmc1_out_stat                         full
% 4.24/1.09  --bmc1_ground_init                      false
% 4.24/1.09  --bmc1_pre_inst_next_state              false
% 4.24/1.09  --bmc1_pre_inst_state                   false
% 4.24/1.09  --bmc1_pre_inst_reach_state             false
% 4.24/1.09  --bmc1_out_unsat_core                   false
% 4.24/1.09  --bmc1_aig_witness_out                  false
% 4.24/1.09  --bmc1_verbose                          false
% 4.24/1.09  --bmc1_dump_clauses_tptp                false
% 4.24/1.09  --bmc1_dump_unsat_core_tptp             false
% 4.24/1.09  --bmc1_dump_file                        -
% 4.24/1.09  --bmc1_ucm_expand_uc_limit              128
% 4.24/1.09  --bmc1_ucm_n_expand_iterations          6
% 4.24/1.09  --bmc1_ucm_extend_mode                  1
% 4.24/1.09  --bmc1_ucm_init_mode                    2
% 4.24/1.09  --bmc1_ucm_cone_mode                    none
% 4.24/1.09  --bmc1_ucm_reduced_relation_type        0
% 4.24/1.09  --bmc1_ucm_relax_model                  4
% 4.24/1.09  --bmc1_ucm_full_tr_after_sat            true
% 4.24/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 4.24/1.09  --bmc1_ucm_layered_model                none
% 4.24/1.09  --bmc1_ucm_max_lemma_size               10
% 4.24/1.09  
% 4.24/1.09  ------ AIG Options
% 4.24/1.09  
% 4.24/1.09  --aig_mode                              false
% 4.24/1.09  
% 4.24/1.09  ------ Instantiation Options
% 4.24/1.09  
% 4.24/1.09  --instantiation_flag                    true
% 4.24/1.09  --inst_sos_flag                         false
% 4.24/1.09  --inst_sos_phase                        true
% 4.24/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.24/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.24/1.09  --inst_lit_sel_side                     num_symb
% 4.24/1.09  --inst_solver_per_active                1400
% 4.24/1.09  --inst_solver_calls_frac                1.
% 4.24/1.09  --inst_passive_queue_type               priority_queues
% 4.24/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.24/1.09  --inst_passive_queues_freq              [25;2]
% 4.24/1.09  --inst_dismatching                      true
% 4.24/1.09  --inst_eager_unprocessed_to_passive     true
% 4.24/1.09  --inst_prop_sim_given                   true
% 4.24/1.09  --inst_prop_sim_new                     false
% 4.24/1.09  --inst_subs_new                         false
% 4.24/1.09  --inst_eq_res_simp                      false
% 4.24/1.09  --inst_subs_given                       false
% 4.24/1.09  --inst_orphan_elimination               true
% 4.24/1.09  --inst_learning_loop_flag               true
% 4.24/1.09  --inst_learning_start                   3000
% 4.24/1.09  --inst_learning_factor                  2
% 4.24/1.09  --inst_start_prop_sim_after_learn       3
% 4.24/1.09  --inst_sel_renew                        solver
% 4.24/1.09  --inst_lit_activity_flag                true
% 4.24/1.09  --inst_restr_to_given                   false
% 4.24/1.09  --inst_activity_threshold               500
% 4.24/1.09  --inst_out_proof                        true
% 4.24/1.09  
% 4.24/1.09  ------ Resolution Options
% 4.24/1.09  
% 4.24/1.09  --resolution_flag                       true
% 4.24/1.09  --res_lit_sel                           adaptive
% 4.24/1.09  --res_lit_sel_side                      none
% 4.24/1.09  --res_ordering                          kbo
% 4.24/1.09  --res_to_prop_solver                    active
% 4.24/1.09  --res_prop_simpl_new                    false
% 4.24/1.09  --res_prop_simpl_given                  true
% 4.24/1.09  --res_passive_queue_type                priority_queues
% 4.24/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.24/1.09  --res_passive_queues_freq               [15;5]
% 4.24/1.09  --res_forward_subs                      full
% 4.24/1.09  --res_backward_subs                     full
% 4.24/1.09  --res_forward_subs_resolution           true
% 4.24/1.09  --res_backward_subs_resolution          true
% 4.24/1.09  --res_orphan_elimination                true
% 4.24/1.09  --res_time_limit                        2.
% 4.24/1.09  --res_out_proof                         true
% 4.24/1.09  
% 4.24/1.09  ------ Superposition Options
% 4.24/1.09  
% 4.24/1.09  --superposition_flag                    true
% 4.24/1.09  --sup_passive_queue_type                priority_queues
% 4.24/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.24/1.09  --sup_passive_queues_freq               [8;1;4]
% 4.24/1.09  --demod_completeness_check              fast
% 4.24/1.09  --demod_use_ground                      true
% 4.24/1.09  --sup_to_prop_solver                    passive
% 4.24/1.09  --sup_prop_simpl_new                    true
% 4.24/1.09  --sup_prop_simpl_given                  true
% 4.24/1.09  --sup_fun_splitting                     false
% 4.24/1.09  --sup_smt_interval                      50000
% 4.24/1.09  
% 4.24/1.09  ------ Superposition Simplification Setup
% 4.24/1.09  
% 4.24/1.09  --sup_indices_passive                   []
% 4.24/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.24/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.24/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.24/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 4.24/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.24/1.09  --sup_full_bw                           [BwDemod]
% 4.24/1.09  --sup_immed_triv                        [TrivRules]
% 4.24/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.24/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.24/1.09  --sup_immed_bw_main                     []
% 4.24/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.24/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 4.24/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.24/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.24/1.09  
% 4.24/1.09  ------ Combination Options
% 4.24/1.09  
% 4.24/1.09  --comb_res_mult                         3
% 4.24/1.09  --comb_sup_mult                         2
% 4.24/1.09  --comb_inst_mult                        10
% 4.24/1.09  
% 4.24/1.09  ------ Debug Options
% 4.24/1.09  
% 4.24/1.09  --dbg_backtrace                         false
% 4.24/1.09  --dbg_dump_prop_clauses                 false
% 4.24/1.09  --dbg_dump_prop_clauses_file            -
% 4.24/1.09  --dbg_out_stat                          false
% 4.24/1.09  ------ Parsing...
% 4.24/1.09  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.24/1.09  
% 4.24/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.24/1.09  
% 4.24/1.09  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.24/1.09  
% 4.24/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.24/1.09  ------ Proving...
% 4.24/1.09  ------ Problem Properties 
% 4.24/1.09  
% 4.24/1.09  
% 4.24/1.09  clauses                                 42
% 4.24/1.09  conjectures                             20
% 4.24/1.09  EPR                                     15
% 4.24/1.09  Horn                                    23
% 4.24/1.09  unary                                   19
% 4.24/1.09  binary                                  1
% 4.24/1.09  lits                                    280
% 4.24/1.09  lits eq                                 2
% 4.24/1.09  fd_pure                                 0
% 4.24/1.09  fd_pseudo                               0
% 4.24/1.09  fd_cond                                 0
% 4.24/1.09  fd_pseudo_cond                          2
% 4.24/1.09  AC symbols                              0
% 4.24/1.09  
% 4.24/1.09  ------ Schedule dynamic 5 is on 
% 4.24/1.09  
% 4.24/1.09  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.24/1.09  
% 4.24/1.09  
% 4.24/1.09  ------ 
% 4.24/1.09  Current options:
% 4.24/1.09  ------ 
% 4.24/1.09  
% 4.24/1.09  ------ Input Options
% 4.24/1.09  
% 4.24/1.09  --out_options                           all
% 4.24/1.09  --tptp_safe_out                         true
% 4.24/1.09  --problem_path                          ""
% 4.24/1.09  --include_path                          ""
% 4.24/1.09  --clausifier                            res/vclausify_rel
% 4.24/1.09  --clausifier_options                    --mode clausify
% 4.24/1.09  --stdin                                 false
% 4.24/1.09  --stats_out                             all
% 4.24/1.09  
% 4.24/1.09  ------ General Options
% 4.24/1.09  
% 4.24/1.09  --fof                                   false
% 4.24/1.09  --time_out_real                         305.
% 4.24/1.09  --time_out_virtual                      -1.
% 4.24/1.09  --symbol_type_check                     false
% 4.24/1.09  --clausify_out                          false
% 4.24/1.09  --sig_cnt_out                           false
% 4.24/1.09  --trig_cnt_out                          false
% 4.24/1.09  --trig_cnt_out_tolerance                1.
% 4.24/1.09  --trig_cnt_out_sk_spl                   false
% 4.24/1.09  --abstr_cl_out                          false
% 4.24/1.09  
% 4.24/1.09  ------ Global Options
% 4.24/1.09  
% 4.24/1.09  --schedule                              default
% 4.24/1.09  --add_important_lit                     false
% 4.24/1.09  --prop_solver_per_cl                    1000
% 4.24/1.09  --min_unsat_core                        false
% 4.24/1.09  --soft_assumptions                      false
% 4.24/1.09  --soft_lemma_size                       3
% 4.24/1.09  --prop_impl_unit_size                   0
% 4.24/1.09  --prop_impl_unit                        []
% 4.24/1.09  --share_sel_clauses                     true
% 4.24/1.09  --reset_solvers                         false
% 4.24/1.09  --bc_imp_inh                            [conj_cone]
% 4.24/1.09  --conj_cone_tolerance                   3.
% 4.24/1.09  --extra_neg_conj                        none
% 4.24/1.09  --large_theory_mode                     true
% 4.24/1.09  --prolific_symb_bound                   200
% 4.24/1.09  --lt_threshold                          2000
% 4.24/1.09  --clause_weak_htbl                      true
% 4.24/1.09  --gc_record_bc_elim                     false
% 4.24/1.09  
% 4.24/1.09  ------ Preprocessing Options
% 4.24/1.09  
% 4.24/1.09  --preprocessing_flag                    true
% 4.24/1.09  --time_out_prep_mult                    0.1
% 4.24/1.09  --splitting_mode                        input
% 4.24/1.09  --splitting_grd                         true
% 4.24/1.09  --splitting_cvd                         false
% 4.24/1.09  --splitting_cvd_svl                     false
% 4.24/1.09  --splitting_nvd                         32
% 4.24/1.09  --sub_typing                            true
% 4.24/1.09  --prep_gs_sim                           true
% 4.24/1.09  --prep_unflatten                        true
% 4.24/1.09  --prep_res_sim                          true
% 4.24/1.09  --prep_upred                            true
% 4.24/1.09  --prep_sem_filter                       exhaustive
% 4.24/1.09  --prep_sem_filter_out                   false
% 4.24/1.09  --pred_elim                             true
% 4.24/1.09  --res_sim_input                         true
% 4.24/1.09  --eq_ax_congr_red                       true
% 4.24/1.09  --pure_diseq_elim                       true
% 4.24/1.09  --brand_transform                       false
% 4.24/1.09  --non_eq_to_eq                          false
% 4.24/1.09  --prep_def_merge                        true
% 4.24/1.09  --prep_def_merge_prop_impl              false
% 4.24/1.09  --prep_def_merge_mbd                    true
% 4.24/1.09  --prep_def_merge_tr_red                 false
% 4.24/1.09  --prep_def_merge_tr_cl                  false
% 4.24/1.09  --smt_preprocessing                     true
% 4.24/1.09  --smt_ac_axioms                         fast
% 4.24/1.09  --preprocessed_out                      false
% 4.24/1.09  --preprocessed_stats                    false
% 4.24/1.09  
% 4.24/1.09  ------ Abstraction refinement Options
% 4.24/1.09  
% 4.24/1.09  --abstr_ref                             []
% 4.24/1.09  --abstr_ref_prep                        false
% 4.24/1.09  --abstr_ref_until_sat                   false
% 4.24/1.09  --abstr_ref_sig_restrict                funpre
% 4.24/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 4.24/1.09  --abstr_ref_under                       []
% 4.24/1.09  
% 4.24/1.09  ------ SAT Options
% 4.24/1.09  
% 4.24/1.09  --sat_mode                              false
% 4.24/1.09  --sat_fm_restart_options                ""
% 4.24/1.09  --sat_gr_def                            false
% 4.24/1.09  --sat_epr_types                         true
% 4.24/1.09  --sat_non_cyclic_types                  false
% 4.24/1.09  --sat_finite_models                     false
% 4.24/1.09  --sat_fm_lemmas                         false
% 4.24/1.09  --sat_fm_prep                           false
% 4.24/1.09  --sat_fm_uc_incr                        true
% 4.24/1.09  --sat_out_model                         small
% 4.24/1.09  --sat_out_clauses                       false
% 4.24/1.09  
% 4.24/1.09  ------ QBF Options
% 4.24/1.09  
% 4.24/1.09  --qbf_mode                              false
% 4.24/1.09  --qbf_elim_univ                         false
% 4.24/1.09  --qbf_dom_inst                          none
% 4.24/1.09  --qbf_dom_pre_inst                      false
% 4.24/1.09  --qbf_sk_in                             false
% 4.24/1.09  --qbf_pred_elim                         true
% 4.24/1.09  --qbf_split                             512
% 4.24/1.09  
% 4.24/1.09  ------ BMC1 Options
% 4.24/1.09  
% 4.24/1.09  --bmc1_incremental                      false
% 4.24/1.09  --bmc1_axioms                           reachable_all
% 4.24/1.09  --bmc1_min_bound                        0
% 4.24/1.09  --bmc1_max_bound                        -1
% 4.24/1.09  --bmc1_max_bound_default                -1
% 4.24/1.09  --bmc1_symbol_reachability              true
% 4.24/1.09  --bmc1_property_lemmas                  false
% 4.24/1.09  --bmc1_k_induction                      false
% 4.24/1.09  --bmc1_non_equiv_states                 false
% 4.24/1.09  --bmc1_deadlock                         false
% 4.24/1.09  --bmc1_ucm                              false
% 4.24/1.09  --bmc1_add_unsat_core                   none
% 4.24/1.09  --bmc1_unsat_core_children              false
% 4.24/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 4.24/1.09  --bmc1_out_stat                         full
% 4.24/1.09  --bmc1_ground_init                      false
% 4.24/1.09  --bmc1_pre_inst_next_state              false
% 4.24/1.09  --bmc1_pre_inst_state                   false
% 4.24/1.09  --bmc1_pre_inst_reach_state             false
% 4.24/1.09  --bmc1_out_unsat_core                   false
% 4.24/1.09  --bmc1_aig_witness_out                  false
% 4.24/1.09  --bmc1_verbose                          false
% 4.24/1.09  --bmc1_dump_clauses_tptp                false
% 4.24/1.09  --bmc1_dump_unsat_core_tptp             false
% 4.24/1.09  --bmc1_dump_file                        -
% 4.24/1.09  --bmc1_ucm_expand_uc_limit              128
% 4.24/1.09  --bmc1_ucm_n_expand_iterations          6
% 4.24/1.09  --bmc1_ucm_extend_mode                  1
% 4.24/1.09  --bmc1_ucm_init_mode                    2
% 4.24/1.09  --bmc1_ucm_cone_mode                    none
% 4.24/1.09  --bmc1_ucm_reduced_relation_type        0
% 4.24/1.09  --bmc1_ucm_relax_model                  4
% 4.24/1.09  --bmc1_ucm_full_tr_after_sat            true
% 4.24/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 4.24/1.09  --bmc1_ucm_layered_model                none
% 4.24/1.09  --bmc1_ucm_max_lemma_size               10
% 4.24/1.09  
% 4.24/1.09  ------ AIG Options
% 4.24/1.09  
% 4.24/1.09  --aig_mode                              false
% 4.24/1.09  
% 4.24/1.09  ------ Instantiation Options
% 4.24/1.09  
% 4.24/1.09  --instantiation_flag                    true
% 4.24/1.09  --inst_sos_flag                         false
% 4.24/1.09  --inst_sos_phase                        true
% 4.24/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.24/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.24/1.09  --inst_lit_sel_side                     none
% 4.24/1.09  --inst_solver_per_active                1400
% 4.24/1.09  --inst_solver_calls_frac                1.
% 4.24/1.09  --inst_passive_queue_type               priority_queues
% 4.24/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.24/1.09  --inst_passive_queues_freq              [25;2]
% 4.24/1.09  --inst_dismatching                      true
% 4.24/1.09  --inst_eager_unprocessed_to_passive     true
% 4.24/1.09  --inst_prop_sim_given                   true
% 4.24/1.09  --inst_prop_sim_new                     false
% 4.24/1.09  --inst_subs_new                         false
% 4.24/1.09  --inst_eq_res_simp                      false
% 4.24/1.09  --inst_subs_given                       false
% 4.24/1.09  --inst_orphan_elimination               true
% 4.24/1.09  --inst_learning_loop_flag               true
% 4.24/1.09  --inst_learning_start                   3000
% 4.24/1.09  --inst_learning_factor                  2
% 4.24/1.09  --inst_start_prop_sim_after_learn       3
% 4.24/1.09  --inst_sel_renew                        solver
% 4.24/1.09  --inst_lit_activity_flag                true
% 4.24/1.09  --inst_restr_to_given                   false
% 4.24/1.09  --inst_activity_threshold               500
% 4.24/1.09  --inst_out_proof                        true
% 4.24/1.09  
% 4.24/1.09  ------ Resolution Options
% 4.24/1.09  
% 4.24/1.09  --resolution_flag                       false
% 4.24/1.09  --res_lit_sel                           adaptive
% 4.24/1.09  --res_lit_sel_side                      none
% 4.24/1.09  --res_ordering                          kbo
% 4.24/1.09  --res_to_prop_solver                    active
% 4.24/1.09  --res_prop_simpl_new                    false
% 4.24/1.09  --res_prop_simpl_given                  true
% 4.24/1.09  --res_passive_queue_type                priority_queues
% 4.24/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.24/1.09  --res_passive_queues_freq               [15;5]
% 4.24/1.09  --res_forward_subs                      full
% 4.24/1.09  --res_backward_subs                     full
% 4.24/1.09  --res_forward_subs_resolution           true
% 4.24/1.09  --res_backward_subs_resolution          true
% 4.24/1.09  --res_orphan_elimination                true
% 4.24/1.09  --res_time_limit                        2.
% 4.24/1.09  --res_out_proof                         true
% 4.24/1.09  
% 4.24/1.09  ------ Superposition Options
% 4.24/1.09  
% 4.24/1.09  --superposition_flag                    true
% 4.24/1.09  --sup_passive_queue_type                priority_queues
% 4.24/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.24/1.09  --sup_passive_queues_freq               [8;1;4]
% 4.24/1.09  --demod_completeness_check              fast
% 4.24/1.09  --demod_use_ground                      true
% 4.24/1.09  --sup_to_prop_solver                    passive
% 4.24/1.09  --sup_prop_simpl_new                    true
% 4.24/1.09  --sup_prop_simpl_given                  true
% 4.24/1.09  --sup_fun_splitting                     false
% 4.24/1.09  --sup_smt_interval                      50000
% 4.24/1.09  
% 4.24/1.09  ------ Superposition Simplification Setup
% 4.24/1.09  
% 4.24/1.09  --sup_indices_passive                   []
% 4.24/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.24/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.24/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.24/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 4.24/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.24/1.09  --sup_full_bw                           [BwDemod]
% 4.24/1.09  --sup_immed_triv                        [TrivRules]
% 4.24/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.24/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.24/1.09  --sup_immed_bw_main                     []
% 4.24/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.24/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 4.24/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.24/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.24/1.09  
% 4.24/1.09  ------ Combination Options
% 4.24/1.09  
% 4.24/1.09  --comb_res_mult                         3
% 4.24/1.09  --comb_sup_mult                         2
% 4.24/1.09  --comb_inst_mult                        10
% 4.24/1.09  
% 4.24/1.09  ------ Debug Options
% 4.24/1.09  
% 4.24/1.09  --dbg_backtrace                         false
% 4.24/1.09  --dbg_dump_prop_clauses                 false
% 4.24/1.09  --dbg_dump_prop_clauses_file            -
% 4.24/1.09  --dbg_out_stat                          false
% 4.24/1.09  
% 4.24/1.09  
% 4.24/1.09  
% 4.24/1.09  
% 4.24/1.09  ------ Proving...
% 4.24/1.09  
% 4.24/1.09  
% 4.24/1.09  % SZS status Theorem for theBenchmark.p
% 4.24/1.09  
% 4.24/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 4.24/1.09  
% 4.24/1.09  fof(f6,axiom,(
% 4.24/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f22,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | (~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.24/1.09    inference(ennf_transformation,[],[f6])).
% 4.24/1.09  
% 4.24/1.09  fof(f23,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(flattening,[],[f22])).
% 4.24/1.09  
% 4.24/1.09  fof(f72,plain,(
% 4.24/1.09    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f23])).
% 4.24/1.09  
% 4.24/1.09  fof(f8,conjecture,(
% 4.24/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f9,negated_conjecture,(
% 4.24/1.09    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 4.24/1.09    inference(negated_conjecture,[],[f8])).
% 4.24/1.09  
% 4.24/1.09  fof(f11,plain,(
% 4.24/1.09    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 4.24/1.09    inference(pure_predicate_removal,[],[f9])).
% 4.24/1.09  
% 4.24/1.09  fof(f25,plain,(
% 4.24/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.24/1.09    inference(ennf_transformation,[],[f11])).
% 4.24/1.09  
% 4.24/1.09  fof(f26,plain,(
% 4.24/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.24/1.09    inference(flattening,[],[f25])).
% 4.24/1.09  
% 4.24/1.09  fof(f44,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 4.24/1.09    introduced(choice_axiom,[])).
% 4.24/1.09  
% 4.24/1.09  fof(f43,plain,(
% 4.24/1.09    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),sK6),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 4.24/1.09    introduced(choice_axiom,[])).
% 4.24/1.09  
% 4.24/1.09  fof(f42,plain,(
% 4.24/1.09    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r4_tsep_1(X0,X2,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,sK5),X4),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,X2,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 4.24/1.09    introduced(choice_axiom,[])).
% 4.24/1.09  
% 4.24/1.09  fof(f41,plain,(
% 4.24/1.09    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r4_tsep_1(X0,sK4,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,sK4,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 4.24/1.09    introduced(choice_axiom,[])).
% 4.24/1.09  
% 4.24/1.09  fof(f40,plain,(
% 4.24/1.09    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,sK3,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 4.24/1.09    introduced(choice_axiom,[])).
% 4.24/1.09  
% 4.24/1.09  fof(f39,plain,(
% 4.24/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 4.24/1.09    introduced(choice_axiom,[])).
% 4.24/1.09  
% 4.24/1.09  fof(f45,plain,(
% 4.24/1.09    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 4.24/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f44,f43,f42,f41,f40,f39])).
% 4.24/1.09  
% 4.24/1.09  fof(f92,plain,(
% 4.24/1.09    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f2,axiom,(
% 4.24/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r1_tsep_1(X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f10,plain,(
% 4.24/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 4.24/1.09    inference(pure_predicate_removal,[],[f2])).
% 4.24/1.09  
% 4.24/1.09  fof(f14,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6))) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.24/1.09    inference(ennf_transformation,[],[f10])).
% 4.24/1.09  
% 4.24/1.09  fof(f15,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(flattening,[],[f14])).
% 4.24/1.09  
% 4.24/1.09  fof(f31,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(nnf_transformation,[],[f15])).
% 4.24/1.09  
% 4.24/1.09  fof(f32,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(flattening,[],[f31])).
% 4.24/1.09  
% 4.24/1.09  fof(f48,plain,(
% 4.24/1.09    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f32])).
% 4.24/1.09  
% 4.24/1.09  fof(f97,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(equality_resolution,[],[f48])).
% 4.24/1.09  
% 4.24/1.09  fof(f3,axiom,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f16,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.24/1.09    inference(ennf_transformation,[],[f3])).
% 4.24/1.09  
% 4.24/1.09  fof(f17,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(flattening,[],[f16])).
% 4.24/1.09  
% 4.24/1.09  fof(f51,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f17])).
% 4.24/1.09  
% 4.24/1.09  fof(f53,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f17])).
% 4.24/1.09  
% 4.24/1.09  fof(f52,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f17])).
% 4.24/1.09  
% 4.24/1.09  fof(f74,plain,(
% 4.24/1.09    ~v2_struct_0(sK2)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f75,plain,(
% 4.24/1.09    v2_pre_topc(sK2)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f76,plain,(
% 4.24/1.09    l1_pre_topc(sK2)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f77,plain,(
% 4.24/1.09    ~v2_struct_0(sK3)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f78,plain,(
% 4.24/1.09    v2_pre_topc(sK3)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f79,plain,(
% 4.24/1.09    l1_pre_topc(sK3)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f80,plain,(
% 4.24/1.09    ~v2_struct_0(sK4)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f81,plain,(
% 4.24/1.09    m1_pre_topc(sK4,sK2)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f82,plain,(
% 4.24/1.09    ~v2_struct_0(sK5)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f83,plain,(
% 4.24/1.09    m1_pre_topc(sK5,sK2)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f84,plain,(
% 4.24/1.09    v1_funct_1(sK6)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f85,plain,(
% 4.24/1.09    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f87,plain,(
% 4.24/1.09    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f88,plain,(
% 4.24/1.09    v1_funct_1(sK7)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f89,plain,(
% 4.24/1.09    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f91,plain,(
% 4.24/1.09    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f4,axiom,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f18,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.24/1.09    inference(ennf_transformation,[],[f4])).
% 4.24/1.09  
% 4.24/1.09  fof(f19,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(flattening,[],[f18])).
% 4.24/1.09  
% 4.24/1.09  fof(f56,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f19])).
% 4.24/1.09  
% 4.24/1.09  fof(f1,axiom,(
% 4.24/1.09    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f12,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.24/1.09    inference(ennf_transformation,[],[f1])).
% 4.24/1.09  
% 4.24/1.09  fof(f13,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.24/1.09    inference(flattening,[],[f12])).
% 4.24/1.09  
% 4.24/1.09  fof(f30,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.24/1.09    inference(nnf_transformation,[],[f13])).
% 4.24/1.09  
% 4.24/1.09  fof(f46,plain,(
% 4.24/1.09    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f30])).
% 4.24/1.09  
% 4.24/1.09  fof(f54,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f19])).
% 4.24/1.09  
% 4.24/1.09  fof(f55,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f19])).
% 4.24/1.09  
% 4.24/1.09  fof(f7,axiom,(
% 4.24/1.09    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f24,plain,(
% 4.24/1.09    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 4.24/1.09    inference(ennf_transformation,[],[f7])).
% 4.24/1.09  
% 4.24/1.09  fof(f73,plain,(
% 4.24/1.09    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f24])).
% 4.24/1.09  
% 4.24/1.09  fof(f27,plain,(
% 4.24/1.09    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 4.24/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.24/1.09  
% 4.24/1.09  fof(f36,plain,(
% 4.24/1.09    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 4.24/1.09    inference(nnf_transformation,[],[f27])).
% 4.24/1.09  
% 4.24/1.09  fof(f37,plain,(
% 4.24/1.09    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 4.24/1.09    inference(flattening,[],[f36])).
% 4.24/1.09  
% 4.24/1.09  fof(f38,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 4.24/1.09    inference(rectify,[],[f37])).
% 4.24/1.09  
% 4.24/1.09  fof(f70,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 4.24/1.09    inference(cnf_transformation,[],[f38])).
% 4.24/1.09  
% 4.24/1.09  fof(f28,plain,(
% 4.24/1.09    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 4.24/1.09    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.24/1.09  
% 4.24/1.09  fof(f33,plain,(
% 4.24/1.09    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 4.24/1.09    inference(nnf_transformation,[],[f28])).
% 4.24/1.09  
% 4.24/1.09  fof(f34,plain,(
% 4.24/1.09    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 4.24/1.09    inference(flattening,[],[f33])).
% 4.24/1.09  
% 4.24/1.09  fof(f35,plain,(
% 4.24/1.09    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 4.24/1.09    inference(rectify,[],[f34])).
% 4.24/1.09  
% 4.24/1.09  fof(f60,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f35])).
% 4.24/1.09  
% 4.24/1.09  fof(f5,axiom,(
% 4.24/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 4.24/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.24/1.09  
% 4.24/1.09  fof(f20,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.24/1.09    inference(ennf_transformation,[],[f5])).
% 4.24/1.09  
% 4.24/1.09  fof(f21,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(flattening,[],[f20])).
% 4.24/1.09  
% 4.24/1.09  fof(f29,plain,(
% 4.24/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.24/1.09    inference(definition_folding,[],[f21,f28,f27])).
% 4.24/1.09  
% 4.24/1.09  fof(f71,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f29])).
% 4.24/1.09  
% 4.24/1.09  fof(f93,plain,(
% 4.24/1.09    r4_tsep_1(sK2,sK4,sK5)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f49,plain,(
% 4.24/1.09    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(cnf_transformation,[],[f32])).
% 4.24/1.09  
% 4.24/1.09  fof(f96,plain,(
% 4.24/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.24/1.09    inference(equality_resolution,[],[f49])).
% 4.24/1.09  
% 4.24/1.09  fof(f86,plain,(
% 4.24/1.09    v5_pre_topc(sK6,sK4,sK3)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f90,plain,(
% 4.24/1.09    v5_pre_topc(sK7,sK5,sK3)),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  fof(f94,plain,(
% 4.24/1.09    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 4.24/1.09    inference(cnf_transformation,[],[f45])).
% 4.24/1.09  
% 4.24/1.09  cnf(c_26,plain,
% 4.24/1.09      ( ~ m1_pre_topc(X0,X1)
% 4.24/1.09      | ~ m1_pre_topc(X2,X1)
% 4.24/1.09      | ~ m1_pre_topc(X3,X2)
% 4.24/1.09      | ~ m1_pre_topc(X3,X1)
% 4.24/1.09      | ~ m1_pre_topc(X0,X2)
% 4.24/1.09      | m1_pre_topc(k1_tsep_1(X1,X3,X0),X2)
% 4.24/1.09      | ~ v2_pre_topc(X1)
% 4.24/1.09      | ~ l1_pre_topc(X1)
% 4.24/1.09      | v2_struct_0(X1)
% 4.24/1.09      | v2_struct_0(X3)
% 4.24/1.09      | v2_struct_0(X2)
% 4.24/1.09      | v2_struct_0(X0) ),
% 4.24/1.09      inference(cnf_transformation,[],[f72]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_1316,plain,
% 4.24/1.09      ( ~ m1_pre_topc(X0_54,X1_54)
% 4.24/1.09      | ~ m1_pre_topc(X2_54,X1_54)
% 4.24/1.09      | ~ m1_pre_topc(X3_54,X2_54)
% 4.24/1.09      | ~ m1_pre_topc(X3_54,X1_54)
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X2_54)
% 4.24/1.09      | m1_pre_topc(k1_tsep_1(X1_54,X3_54,X0_54),X2_54)
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(X3_54)
% 4.24/1.09      | v2_struct_0(X2_54) ),
% 4.24/1.09      inference(subtyping,[status(esa)],[c_26]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2049,plain,
% 4.24/1.09      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X3_54,X1_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(k1_tsep_1(X1_54,X3_54,X0_54),X2_54) = iProver_top
% 4.24/1.09      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X0_54) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_30,negated_conjecture,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
% 4.24/1.09      inference(cnf_transformation,[],[f92]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_1313,negated_conjecture,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
% 4.24/1.09      inference(subtyping,[status(esa)],[c_30]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2052,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_4,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
% 4.24/1.09      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
% 4.24/1.09      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
% 4.24/1.09      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 4.24/1.09      | ~ v1_funct_2(k10_tmap_1(X2,X1,X0,X3,X4,X5),u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
% 4.24/1.09      | ~ m1_pre_topc(X3,X2)
% 4.24/1.09      | ~ m1_pre_topc(X0,X2)
% 4.24/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 4.24/1.09      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.24/1.09      | ~ m1_subset_1(k10_tmap_1(X2,X1,X0,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 4.24/1.09      | ~ v2_pre_topc(X1)
% 4.24/1.09      | ~ v2_pre_topc(X2)
% 4.24/1.09      | ~ l1_pre_topc(X1)
% 4.24/1.09      | ~ l1_pre_topc(X2)
% 4.24/1.09      | v2_struct_0(X2)
% 4.24/1.09      | v2_struct_0(X1)
% 4.24/1.09      | v2_struct_0(X0)
% 4.24/1.09      | v2_struct_0(X3)
% 4.24/1.09      | ~ v1_funct_1(X5)
% 4.24/1.09      | ~ v1_funct_1(X4)
% 4.24/1.09      | ~ v1_funct_1(k10_tmap_1(X2,X1,X0,X3,X4,X5)) ),
% 4.24/1.09      inference(cnf_transformation,[],[f97]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_1323,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53)
% 4.24/1.09      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53))
% 4.24/1.09      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.09      | ~ v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54))
% 4.24/1.09      | ~ v1_funct_2(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54))
% 4.24/1.09      | ~ m1_pre_topc(X3_54,X2_54)
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X2_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ m1_subset_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ v2_pre_topc(X2_54)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(X2_54)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(X3_54)
% 4.24/1.09      | v2_struct_0(X2_54)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(X1_53)
% 4.24/1.09      | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) ),
% 4.24/1.09      inference(subtyping,[status(esa)],[c_4]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2042,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53) = iProver_top
% 4.24/1.09      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53)) != iProver_top
% 4.24/1.09      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | v1_funct_2(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 4.24/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | m1_subset_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | v2_pre_topc(X2_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X2_54) != iProver_top
% 4.24/1.09      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.09      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.09      | v1_funct_1(X1_53) != iProver_top
% 4.24/1.09      | v1_funct_1(k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_7,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.24/1.09      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 4.24/1.09      | ~ m1_pre_topc(X1,X5)
% 4.24/1.09      | ~ m1_pre_topc(X4,X5)
% 4.24/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.24/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 4.24/1.09      | ~ v2_pre_topc(X2)
% 4.24/1.09      | ~ v2_pre_topc(X5)
% 4.24/1.09      | ~ l1_pre_topc(X2)
% 4.24/1.09      | ~ l1_pre_topc(X5)
% 4.24/1.09      | v2_struct_0(X5)
% 4.24/1.09      | v2_struct_0(X2)
% 4.24/1.09      | v2_struct_0(X4)
% 4.24/1.09      | v2_struct_0(X1)
% 4.24/1.09      | ~ v1_funct_1(X0)
% 4.24/1.09      | ~ v1_funct_1(X3)
% 4.24/1.09      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 4.24/1.09      inference(cnf_transformation,[],[f51]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_1320,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.09      | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 4.24/1.09      | ~ m1_pre_topc(X2_54,X3_54)
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X3_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ v2_pre_topc(X3_54)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(X3_54)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(X3_54)
% 4.24/1.09      | v2_struct_0(X2_54)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(X1_53)
% 4.24/1.09      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) ),
% 4.24/1.09      inference(subtyping,[status(esa)],[c_7]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2045,plain,
% 4.24/1.09      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.24/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | v2_pre_topc(X3_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X3_54) != iProver_top
% 4.24/1.09      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.09      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.09      | v1_funct_1(X1_53) != iProver_top
% 4.24/1.09      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53)) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_5,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.24/1.09      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 4.24/1.09      | ~ m1_pre_topc(X1,X5)
% 4.24/1.09      | ~ m1_pre_topc(X4,X5)
% 4.24/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.24/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 4.24/1.09      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 4.24/1.09      | ~ v2_pre_topc(X2)
% 4.24/1.09      | ~ v2_pre_topc(X5)
% 4.24/1.09      | ~ l1_pre_topc(X2)
% 4.24/1.09      | ~ l1_pre_topc(X5)
% 4.24/1.09      | v2_struct_0(X5)
% 4.24/1.09      | v2_struct_0(X2)
% 4.24/1.09      | v2_struct_0(X4)
% 4.24/1.09      | v2_struct_0(X1)
% 4.24/1.09      | ~ v1_funct_1(X0)
% 4.24/1.09      | ~ v1_funct_1(X3) ),
% 4.24/1.09      inference(cnf_transformation,[],[f53]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_1322,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.09      | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 4.24/1.09      | ~ m1_pre_topc(X2_54,X3_54)
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X3_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.24/1.09      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ v2_pre_topc(X3_54)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(X3_54)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(X3_54)
% 4.24/1.09      | v2_struct_0(X2_54)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(X1_53) ),
% 4.24/1.09      inference(subtyping,[status(esa)],[c_5]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2043,plain,
% 4.24/1.09      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.24/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)))) = iProver_top
% 4.24/1.09      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | v2_pre_topc(X3_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X3_54) != iProver_top
% 4.24/1.09      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.09      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.09      | v1_funct_1(X1_53) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_6,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.24/1.09      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 4.24/1.09      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 4.24/1.09      | ~ m1_pre_topc(X1,X5)
% 4.24/1.09      | ~ m1_pre_topc(X4,X5)
% 4.24/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.24/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 4.24/1.09      | ~ v2_pre_topc(X2)
% 4.24/1.09      | ~ v2_pre_topc(X5)
% 4.24/1.09      | ~ l1_pre_topc(X2)
% 4.24/1.09      | ~ l1_pre_topc(X5)
% 4.24/1.09      | v2_struct_0(X5)
% 4.24/1.09      | v2_struct_0(X2)
% 4.24/1.09      | v2_struct_0(X4)
% 4.24/1.09      | v2_struct_0(X1)
% 4.24/1.09      | ~ v1_funct_1(X0)
% 4.24/1.09      | ~ v1_funct_1(X3) ),
% 4.24/1.09      inference(cnf_transformation,[],[f52]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_1321,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.09      | ~ v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 4.24/1.09      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))
% 4.24/1.09      | ~ m1_pre_topc(X2_54,X3_54)
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X3_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ v2_pre_topc(X3_54)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(X3_54)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(X3_54)
% 4.24/1.09      | v2_struct_0(X2_54)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(X1_53) ),
% 4.24/1.09      inference(subtyping,[status(esa)],[c_6]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2044,plain,
% 4.24/1.09      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | v1_funct_2(X1_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)) = iProver_top
% 4.24/1.09      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.24/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | v2_pre_topc(X3_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X3_54) != iProver_top
% 4.24/1.09      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.09      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.09      | v1_funct_1(X1_53) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2571,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X0_54,X3_54),X0_54,k10_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53,X1_53)),X0_53) = iProver_top
% 4.24/1.09      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X0_54,X3_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X0_54,X3_54),X0_53),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X0_54,X3_54),X1_53)) != iProver_top
% 4.24/1.09      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.09      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 4.24/1.09      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 4.24/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | v2_pre_topc(X2_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.09      | l1_pre_topc(X2_54) != iProver_top
% 4.24/1.09      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.09      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.09      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.09      | v1_funct_1(X1_53) != iProver_top ),
% 4.24/1.09      inference(forward_subsumption_resolution,
% 4.24/1.09                [status(thm)],
% 4.24/1.09                [c_2042,c_2045,c_2043,c_2044]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_9492,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
% 4.24/1.09      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.09      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.09      | v2_struct_0(sK5) = iProver_top
% 4.24/1.09      | v2_struct_0(sK4) = iProver_top
% 4.24/1.09      | v2_struct_0(sK3) = iProver_top
% 4.24/1.09      | v2_struct_0(sK2) = iProver_top
% 4.24/1.09      | v1_funct_1(sK7) != iProver_top
% 4.24/1.09      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.09      inference(superposition,[status(thm)],[c_2052,c_2571]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_48,negated_conjecture,
% 4.24/1.09      ( ~ v2_struct_0(sK2) ),
% 4.24/1.09      inference(cnf_transformation,[],[f74]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_49,plain,
% 4.24/1.09      ( v2_struct_0(sK2) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_47,negated_conjecture,
% 4.24/1.09      ( v2_pre_topc(sK2) ),
% 4.24/1.09      inference(cnf_transformation,[],[f75]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_50,plain,
% 4.24/1.09      ( v2_pre_topc(sK2) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_46,negated_conjecture,
% 4.24/1.09      ( l1_pre_topc(sK2) ),
% 4.24/1.09      inference(cnf_transformation,[],[f76]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_51,plain,
% 4.24/1.09      ( l1_pre_topc(sK2) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_45,negated_conjecture,
% 4.24/1.09      ( ~ v2_struct_0(sK3) ),
% 4.24/1.09      inference(cnf_transformation,[],[f77]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_52,plain,
% 4.24/1.09      ( v2_struct_0(sK3) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_44,negated_conjecture,
% 4.24/1.09      ( v2_pre_topc(sK3) ),
% 4.24/1.09      inference(cnf_transformation,[],[f78]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_53,plain,
% 4.24/1.09      ( v2_pre_topc(sK3) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_43,negated_conjecture,
% 4.24/1.09      ( l1_pre_topc(sK3) ),
% 4.24/1.09      inference(cnf_transformation,[],[f79]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_54,plain,
% 4.24/1.09      ( l1_pre_topc(sK3) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_42,negated_conjecture,
% 4.24/1.09      ( ~ v2_struct_0(sK4) ),
% 4.24/1.09      inference(cnf_transformation,[],[f80]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_55,plain,
% 4.24/1.09      ( v2_struct_0(sK4) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_41,negated_conjecture,
% 4.24/1.09      ( m1_pre_topc(sK4,sK2) ),
% 4.24/1.09      inference(cnf_transformation,[],[f81]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_56,plain,
% 4.24/1.09      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_40,negated_conjecture,
% 4.24/1.09      ( ~ v2_struct_0(sK5) ),
% 4.24/1.09      inference(cnf_transformation,[],[f82]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_57,plain,
% 4.24/1.09      ( v2_struct_0(sK5) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_39,negated_conjecture,
% 4.24/1.09      ( m1_pre_topc(sK5,sK2) ),
% 4.24/1.09      inference(cnf_transformation,[],[f83]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_58,plain,
% 4.24/1.09      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_38,negated_conjecture,
% 4.24/1.09      ( v1_funct_1(sK6) ),
% 4.24/1.09      inference(cnf_transformation,[],[f84]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_59,plain,
% 4.24/1.09      ( v1_funct_1(sK6) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_37,negated_conjecture,
% 4.24/1.09      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 4.24/1.09      inference(cnf_transformation,[],[f85]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_60,plain,
% 4.24/1.09      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_35,negated_conjecture,
% 4.24/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 4.24/1.09      inference(cnf_transformation,[],[f87]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_62,plain,
% 4.24/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_34,negated_conjecture,
% 4.24/1.09      ( v1_funct_1(sK7) ),
% 4.24/1.09      inference(cnf_transformation,[],[f88]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_63,plain,
% 4.24/1.09      ( v1_funct_1(sK7) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_33,negated_conjecture,
% 4.24/1.09      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 4.24/1.09      inference(cnf_transformation,[],[f89]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_64,plain,
% 4.24/1.09      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_31,negated_conjecture,
% 4.24/1.09      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 4.24/1.09      inference(cnf_transformation,[],[f91]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_66,plain,
% 4.24/1.09      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_67,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2813,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X1_54)
% 4.24/1.09      | ~ m1_pre_topc(sK5,X1_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_53,sK7))
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_1320]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3055,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X0_54,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | v1_funct_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7))
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_2813]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3575,plain,
% 4.24/1.09      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK4)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 4.24/1.09      | ~ v1_funct_1(sK7)
% 4.24/1.09      | ~ v1_funct_1(sK6) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_3055]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3576,plain,
% 4.24/1.09      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.09      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.09      | v2_struct_0(sK5) = iProver_top
% 4.24/1.09      | v2_struct_0(sK4) = iProver_top
% 4.24/1.09      | v2_struct_0(sK3) = iProver_top
% 4.24/1.09      | v2_struct_0(sK2) = iProver_top
% 4.24/1.09      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 4.24/1.09      | v1_funct_1(sK7) != iProver_top
% 4.24/1.09      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_3575]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2823,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.09      | v1_funct_2(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X1_54)
% 4.24/1.09      | ~ m1_pre_topc(sK5,X1_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_1321]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3073,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.09      | v1_funct_2(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X0_54,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_2823]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3584,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.09      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK4)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_3073]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3586,plain,
% 4.24/1.09      ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 4.24/1.09      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.09      | v2_struct_0(sK5) = iProver_top
% 4.24/1.09      | v2_struct_0(sK4) = iProver_top
% 4.24/1.09      | v2_struct_0(sK3) = iProver_top
% 4.24/1.09      | v2_struct_0(sK2) = iProver_top
% 4.24/1.09      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.09      | v1_funct_1(sK7) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_3584]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3588,plain,
% 4.24/1.09      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 4.24/1.09      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.09      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.09      | v2_struct_0(sK5) = iProver_top
% 4.24/1.09      | v2_struct_0(sK4) = iProver_top
% 4.24/1.09      | v2_struct_0(sK3) = iProver_top
% 4.24/1.09      | v2_struct_0(sK2) = iProver_top
% 4.24/1.09      | v1_funct_1(sK7) != iProver_top
% 4.24/1.09      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_3586]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2833,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X0_54,X1_54)
% 4.24/1.09      | ~ m1_pre_topc(sK5,X1_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.09      | m1_subset_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(X1_54)
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(X1_54)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_1322]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3087,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X0_54,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.09      | m1_subset_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_2833]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3748,plain,
% 4.24/1.09      ( ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.09      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK4)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(sK7) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_3087]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3749,plain,
% 4.24/1.09      ( v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 4.24/1.09      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.09      | v2_struct_0(sK5) = iProver_top
% 4.24/1.09      | v2_struct_0(sK4) = iProver_top
% 4.24/1.09      | v2_struct_0(sK3) = iProver_top
% 4.24/1.09      | v2_struct_0(sK2) = iProver_top
% 4.24/1.09      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.09      | v1_funct_1(sK7) != iProver_top ),
% 4.24/1.09      inference(predicate_to_equality,[status(thm)],[c_3748]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3751,plain,
% 4.24/1.09      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.09      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 4.24/1.09      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.09      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.09      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.09      | v2_struct_0(sK5) = iProver_top
% 4.24/1.09      | v2_struct_0(sK4) = iProver_top
% 4.24/1.09      | v2_struct_0(sK3) = iProver_top
% 4.24/1.09      | v2_struct_0(sK2) = iProver_top
% 4.24/1.09      | v1_funct_1(sK7) != iProver_top
% 4.24/1.09      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_3749]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_2858,plain,
% 4.24/1.09      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_54,sK4,X1_54)),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,sK4,k2_tsep_1(X0_54,sK4,X1_54),sK6),k3_tmap_1(X0_54,sK3,X1_54,k2_tsep_1(X0_54,sK4,X1_54),X0_53))
% 4.24/1.09      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,k1_tsep_1(X0_54,sK4,X1_54),sK4,k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53)),sK6)
% 4.24/1.09      | ~ v1_funct_2(X0_53,u1_struct_0(X1_54),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53),u1_struct_0(k1_tsep_1(X0_54,sK4,X1_54)),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X1_54,X0_54)
% 4.24/1.09      | ~ m1_pre_topc(sK4,X0_54)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,X1_54)),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(X0_54)
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(X0_54)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | v2_struct_0(X1_54)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK4)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,X1_54,sK6,X0_53))
% 4.24/1.09      | ~ v1_funct_1(sK6) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_1323]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3108,plain,
% 4.24/1.09      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,X0_54)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,X0_54),sK6),k3_tmap_1(sK2,sK3,X0_54,k2_tsep_1(sK2,sK4,X0_54),X0_53))
% 4.24/1.09      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X0_54),sK4,k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53)),sK6)
% 4.24/1.09      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(X0_54,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_54)),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(X0_54)
% 4.24/1.09      | v2_struct_0(sK4)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,X0_54,sK6,X0_53))
% 4.24/1.09      | ~ v1_funct_1(sK6) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_2858]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_3897,plain,
% 4.24/1.09      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),X0_53))
% 4.24/1.09      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53)),sK6)
% 4.24/1.09      | ~ v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK4)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(X0_53)
% 4.24/1.09      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_53))
% 4.24/1.09      | ~ v1_funct_1(sK6) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_3108]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_6820,plain,
% 4.24/1.09      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
% 4.24/1.09      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
% 4.24/1.09      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.09      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.09      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.09      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.09      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.09      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.09      | ~ v2_pre_topc(sK3)
% 4.24/1.09      | ~ v2_pre_topc(sK2)
% 4.24/1.09      | ~ l1_pre_topc(sK3)
% 4.24/1.09      | ~ l1_pre_topc(sK2)
% 4.24/1.09      | v2_struct_0(sK5)
% 4.24/1.09      | v2_struct_0(sK4)
% 4.24/1.09      | v2_struct_0(sK3)
% 4.24/1.09      | v2_struct_0(sK2)
% 4.24/1.09      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 4.24/1.09      | ~ v1_funct_1(sK7)
% 4.24/1.09      | ~ v1_funct_1(sK6) ),
% 4.24/1.09      inference(instantiation,[status(thm)],[c_3897]) ).
% 4.24/1.09  
% 4.24/1.09  cnf(c_6821,plain,
% 4.24/1.09      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 4.24/1.09      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
% 4.24/1.09      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.09      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK5) = iProver_top
% 4.24/1.10      | v2_struct_0(sK4) = iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 4.24/1.10      | v1_funct_1(sK7) != iProver_top
% 4.24/1.10      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_6820]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9530,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_9492,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 4.24/1.10                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_3576,c_3588,
% 4.24/1.10                 c_3751,c_6821]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_8,plain,
% 4.24/1.10      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.24/1.10      | ~ m1_pre_topc(X3,X4)
% 4.24/1.10      | ~ m1_pre_topc(X1,X4)
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.24/1.10      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 4.24/1.10      | ~ v2_pre_topc(X2)
% 4.24/1.10      | ~ v2_pre_topc(X4)
% 4.24/1.10      | ~ l1_pre_topc(X2)
% 4.24/1.10      | ~ l1_pre_topc(X4)
% 4.24/1.10      | v2_struct_0(X4)
% 4.24/1.10      | v2_struct_0(X2)
% 4.24/1.10      | ~ v1_funct_1(X0) ),
% 4.24/1.10      inference(cnf_transformation,[],[f56]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1319,plain,
% 4.24/1.10      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.10      | ~ m1_pre_topc(X2_54,X3_54)
% 4.24/1.10      | ~ m1_pre_topc(X0_54,X3_54)
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.10      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.24/1.10      | ~ v2_pre_topc(X1_54)
% 4.24/1.10      | ~ v2_pre_topc(X3_54)
% 4.24/1.10      | ~ l1_pre_topc(X1_54)
% 4.24/1.10      | ~ l1_pre_topc(X3_54)
% 4.24/1.10      | v2_struct_0(X1_54)
% 4.24/1.10      | v2_struct_0(X3_54)
% 4.24/1.10      | ~ v1_funct_1(X0_53) ),
% 4.24/1.10      inference(subtyping,[status(esa)],[c_8]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2046,plain,
% 4.24/1.10      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.24/1.10      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 4.24/1.10      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(X3_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X3_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1,plain,
% 4.24/1.10      ( ~ r2_funct_2(X0,X1,X2,X3)
% 4.24/1.10      | ~ v1_funct_2(X3,X0,X1)
% 4.24/1.10      | ~ v1_funct_2(X2,X0,X1)
% 4.24/1.10      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.24/1.10      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.24/1.10      | ~ v1_funct_1(X3)
% 4.24/1.10      | ~ v1_funct_1(X2)
% 4.24/1.10      | X2 = X3 ),
% 4.24/1.10      inference(cnf_transformation,[],[f46]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1326,plain,
% 4.24/1.10      ( ~ r2_funct_2(X0_55,X1_55,X0_53,X1_53)
% 4.24/1.10      | ~ v1_funct_2(X1_53,X0_55,X1_55)
% 4.24/1.10      | ~ v1_funct_2(X0_53,X0_55,X1_55)
% 4.24/1.10      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 4.24/1.10      | ~ v1_funct_1(X0_53)
% 4.24/1.10      | ~ v1_funct_1(X1_53)
% 4.24/1.10      | X0_53 = X1_53 ),
% 4.24/1.10      inference(subtyping,[status(esa)],[c_1]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2039,plain,
% 4.24/1.10      ( X0_53 = X1_53
% 4.24/1.10      | r2_funct_2(X0_55,X1_55,X0_53,X1_53) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,X0_55,X1_55) != iProver_top
% 4.24/1.10      | v1_funct_2(X1_53,X0_55,X1_55) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 4.24/1.10      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(X1_53) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_4280,plain,
% 4.24/1.10      ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
% 4.24/1.10      | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(X3_54,X0_54) != iProver_top
% 4.24/1.10      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(X1_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53)) != iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_2046,c_2039]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_10,plain,
% 4.24/1.10      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.24/1.10      | ~ m1_pre_topc(X3,X4)
% 4.24/1.10      | ~ m1_pre_topc(X1,X4)
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.24/1.10      | ~ v2_pre_topc(X2)
% 4.24/1.10      | ~ v2_pre_topc(X4)
% 4.24/1.10      | ~ l1_pre_topc(X2)
% 4.24/1.10      | ~ l1_pre_topc(X4)
% 4.24/1.10      | v2_struct_0(X4)
% 4.24/1.10      | v2_struct_0(X2)
% 4.24/1.10      | ~ v1_funct_1(X0)
% 4.24/1.10      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 4.24/1.10      inference(cnf_transformation,[],[f54]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1317,plain,
% 4.24/1.10      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.10      | ~ m1_pre_topc(X2_54,X3_54)
% 4.24/1.10      | ~ m1_pre_topc(X0_54,X3_54)
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.10      | ~ v2_pre_topc(X1_54)
% 4.24/1.10      | ~ v2_pre_topc(X3_54)
% 4.24/1.10      | ~ l1_pre_topc(X1_54)
% 4.24/1.10      | ~ l1_pre_topc(X3_54)
% 4.24/1.10      | v2_struct_0(X1_54)
% 4.24/1.10      | v2_struct_0(X3_54)
% 4.24/1.10      | ~ v1_funct_1(X0_53)
% 4.24/1.10      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)) ),
% 4.24/1.10      inference(subtyping,[status(esa)],[c_10]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2048,plain,
% 4.24/1.10      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.24/1.10      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(X3_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X3_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_53)) = iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9,plain,
% 4.24/1.10      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.24/1.10      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 4.24/1.10      | ~ m1_pre_topc(X4,X3)
% 4.24/1.10      | ~ m1_pre_topc(X1,X3)
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.24/1.10      | ~ v2_pre_topc(X2)
% 4.24/1.10      | ~ v2_pre_topc(X3)
% 4.24/1.10      | ~ l1_pre_topc(X2)
% 4.24/1.10      | ~ l1_pre_topc(X3)
% 4.24/1.10      | v2_struct_0(X3)
% 4.24/1.10      | v2_struct_0(X2)
% 4.24/1.10      | ~ v1_funct_1(X0) ),
% 4.24/1.10      inference(cnf_transformation,[],[f55]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1318,plain,
% 4.24/1.10      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.10      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54))
% 4.24/1.10      | ~ m1_pre_topc(X3_54,X2_54)
% 4.24/1.10      | ~ m1_pre_topc(X0_54,X2_54)
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.10      | ~ v2_pre_topc(X1_54)
% 4.24/1.10      | ~ v2_pre_topc(X2_54)
% 4.24/1.10      | ~ l1_pre_topc(X1_54)
% 4.24/1.10      | ~ l1_pre_topc(X2_54)
% 4.24/1.10      | v2_struct_0(X1_54)
% 4.24/1.10      | v2_struct_0(X2_54)
% 4.24/1.10      | ~ v1_funct_1(X0_53) ),
% 4.24/1.10      inference(subtyping,[status(esa)],[c_9]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2047,plain,
% 4.24/1.10      ( v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_53),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
% 4.24/1.10      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 4.24/1.10      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(X2_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X2_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_7546,plain,
% 4.24/1.10      ( k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53) = X1_53
% 4.24/1.10      | r2_funct_2(u1_struct_0(X3_54),u1_struct_0(X1_54),k3_tmap_1(X0_54,X1_54,X2_54,X3_54,X0_53),X1_53) != iProver_top
% 4.24/1.10      | v1_funct_2(X1_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(X3_54,X0_54) != iProver_top
% 4.24/1.10      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 4.24/1.10      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(X1_53) != iProver_top ),
% 4.24/1.10      inference(forward_subsumption_resolution,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_4280,c_2048,c_2047]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9535,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 4.24/1.10      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 4.24/1.10      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_9530,c_7546]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9730,plain,
% 4.24/1.10      ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_9535,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 4.24/1.10                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_3576,c_3588,c_3751]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9731,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top ),
% 4.24/1.10      inference(renaming,[status(thm)],[c_9730]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9736,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK5) = iProver_top
% 4.24/1.10      | v2_struct_0(sK4) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_2049,c_9731]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_27,plain,
% 4.24/1.10      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 4.24/1.10      inference(cnf_transformation,[],[f73]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1315,plain,
% 4.24/1.10      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 4.24/1.10      inference(subtyping,[status(esa)],[c_27]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_3726,plain,
% 4.24/1.10      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 4.24/1.10      inference(instantiation,[status(thm)],[c_1315]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_3731,plain,
% 4.24/1.10      ( m1_pre_topc(sK2,sK2) = iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_3726]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9788,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_9736,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_3731]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_16,plain,
% 4.24/1.10      ( sP0(X0,X1,X2,X3,X4)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 4.24/1.10      inference(cnf_transformation,[],[f70]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_12,plain,
% 4.24/1.10      ( ~ sP1(X0,X1,X2,X3,X4)
% 4.24/1.10      | ~ sP0(X4,X3,X2,X1,X0)
% 4.24/1.10      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 4.24/1.10      inference(cnf_transformation,[],[f60]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_25,plain,
% 4.24/1.10      ( sP1(X0,X1,X2,X3,X4)
% 4.24/1.10      | ~ r4_tsep_1(X0,X1,X3)
% 4.24/1.10      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 4.24/1.10      | ~ m1_pre_topc(X3,X0)
% 4.24/1.10      | ~ m1_pre_topc(X1,X0)
% 4.24/1.10      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 4.24/1.10      | ~ v2_pre_topc(X4)
% 4.24/1.10      | ~ v2_pre_topc(X0)
% 4.24/1.10      | ~ l1_pre_topc(X4)
% 4.24/1.10      | ~ l1_pre_topc(X0)
% 4.24/1.10      | v2_struct_0(X0)
% 4.24/1.10      | v2_struct_0(X4)
% 4.24/1.10      | v2_struct_0(X1)
% 4.24/1.10      | v2_struct_0(X3)
% 4.24/1.10      | ~ v1_funct_1(X2) ),
% 4.24/1.10      inference(cnf_transformation,[],[f71]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_29,negated_conjecture,
% 4.24/1.10      ( r4_tsep_1(sK2,sK4,sK5) ),
% 4.24/1.10      inference(cnf_transformation,[],[f93]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_516,plain,
% 4.24/1.10      ( sP1(X0,X1,X2,X3,X4)
% 4.24/1.10      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 4.24/1.10      | ~ m1_pre_topc(X3,X0)
% 4.24/1.10      | ~ m1_pre_topc(X1,X0)
% 4.24/1.10      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 4.24/1.10      | ~ v2_pre_topc(X0)
% 4.24/1.10      | ~ v2_pre_topc(X4)
% 4.24/1.10      | ~ l1_pre_topc(X0)
% 4.24/1.10      | ~ l1_pre_topc(X4)
% 4.24/1.10      | v2_struct_0(X0)
% 4.24/1.10      | v2_struct_0(X1)
% 4.24/1.10      | v2_struct_0(X3)
% 4.24/1.10      | v2_struct_0(X4)
% 4.24/1.10      | ~ v1_funct_1(X2)
% 4.24/1.10      | sK5 != X3
% 4.24/1.10      | sK4 != X1
% 4.24/1.10      | sK2 != X0 ),
% 4.24/1.10      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_517,plain,
% 4.24/1.10      ( sP1(sK2,sK4,X0,sK5,X1)
% 4.24/1.10      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 4.24/1.10      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.10      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 4.24/1.10      | ~ v2_pre_topc(X1)
% 4.24/1.10      | ~ v2_pre_topc(sK2)
% 4.24/1.10      | ~ l1_pre_topc(X1)
% 4.24/1.10      | ~ l1_pre_topc(sK2)
% 4.24/1.10      | v2_struct_0(X1)
% 4.24/1.10      | v2_struct_0(sK5)
% 4.24/1.10      | v2_struct_0(sK4)
% 4.24/1.10      | v2_struct_0(sK2)
% 4.24/1.10      | ~ v1_funct_1(X0) ),
% 4.24/1.10      inference(unflattening,[status(thm)],[c_516]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_521,plain,
% 4.24/1.10      ( v2_struct_0(X1)
% 4.24/1.10      | ~ v2_pre_topc(X1)
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 4.24/1.10      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 4.24/1.10      | sP1(sK2,sK4,X0,sK5,X1)
% 4.24/1.10      | ~ l1_pre_topc(X1)
% 4.24/1.10      | ~ v1_funct_1(X0) ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_517,c_48,c_47,c_46,c_42,c_41,c_40,c_39]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_522,plain,
% 4.24/1.10      ( sP1(sK2,sK4,X0,sK5,X1)
% 4.24/1.10      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 4.24/1.10      | ~ v2_pre_topc(X1)
% 4.24/1.10      | ~ l1_pre_topc(X1)
% 4.24/1.10      | v2_struct_0(X1)
% 4.24/1.10      | ~ v1_funct_1(X0) ),
% 4.24/1.10      inference(renaming,[status(thm)],[c_521]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_591,plain,
% 4.24/1.10      ( ~ sP0(X0,X1,X2,X3,X4)
% 4.24/1.10      | v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
% 4.24/1.10      | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
% 4.24/1.10      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
% 4.24/1.10      | ~ v2_pre_topc(X6)
% 4.24/1.10      | ~ l1_pre_topc(X6)
% 4.24/1.10      | v2_struct_0(X6)
% 4.24/1.10      | ~ v1_funct_1(X5)
% 4.24/1.10      | X5 != X2
% 4.24/1.10      | X6 != X0
% 4.24/1.10      | sK5 != X1
% 4.24/1.10      | sK4 != X3
% 4.24/1.10      | sK2 != X4 ),
% 4.24/1.10      inference(resolution_lifted,[status(thm)],[c_12,c_522]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_592,plain,
% 4.24/1.10      ( ~ sP0(X0,sK5,X1,sK4,sK2)
% 4.24/1.10      | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
% 4.24/1.10      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
% 4.24/1.10      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
% 4.24/1.10      | ~ v2_pre_topc(X0)
% 4.24/1.10      | ~ l1_pre_topc(X0)
% 4.24/1.10      | v2_struct_0(X0)
% 4.24/1.10      | ~ v1_funct_1(X1) ),
% 4.24/1.10      inference(unflattening,[status(thm)],[c_591]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_650,plain,
% 4.24/1.10      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),X5,X3)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),X4,X3)
% 4.24/1.10      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
% 4.24/1.10      | ~ v2_pre_topc(X1)
% 4.24/1.10      | ~ l1_pre_topc(X1)
% 4.24/1.10      | v2_struct_0(X1)
% 4.24/1.10      | ~ v1_funct_1(X0)
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6))
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
% 4.24/1.10      | X0 != X6
% 4.24/1.10      | X1 != X3
% 4.24/1.10      | sK5 != X5
% 4.24/1.10      | sK4 != X4
% 4.24/1.10      | sK2 != X2 ),
% 4.24/1.10      inference(resolution_lifted,[status(thm)],[c_16,c_592]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_651,plain,
% 4.24/1.10      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),sK5,X1)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),sK4,X1)
% 4.24/1.10      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
% 4.24/1.10      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 4.24/1.10      | ~ v2_pre_topc(X1)
% 4.24/1.10      | ~ l1_pre_topc(X1)
% 4.24/1.10      | v2_struct_0(X1)
% 4.24/1.10      | ~ v1_funct_1(X0)
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0))
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
% 4.24/1.10      inference(unflattening,[status(thm)],[c_650]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1294,plain,
% 4.24/1.10      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54)
% 4.24/1.10      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54)
% 4.24/1.10      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54))
% 4.24/1.10      | ~ v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54))
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54))))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54))))
% 4.24/1.10      | ~ m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 4.24/1.10      | ~ v2_pre_topc(X0_54)
% 4.24/1.10      | ~ l1_pre_topc(X0_54)
% 4.24/1.10      | v2_struct_0(X0_54)
% 4.24/1.10      | ~ v1_funct_1(X0_53)
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53))
% 4.24/1.10      | ~ v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) ),
% 4.24/1.10      inference(subtyping,[status(esa)],[c_651]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2071,plain,
% 4.24/1.10      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_5867,plain,
% 4.24/1.10      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_2046,c_2071]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_10011,plain,
% 4.24/1.10      ( v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v2_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_5867,c_49,c_50,c_51,c_58]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_10012,plain,
% 4.24/1.10      ( v5_pre_topc(X0_53,k1_tsep_1(sK2,sK4,sK5),X0_54) = iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_54) != iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_54) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X0_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 4.24/1.10      inference(renaming,[status(thm)],[c_10011]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_10034,plain,
% 4.24/1.10      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
% 4.24/1.10      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 4.24/1.10      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 4.24/1.10      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_9788,c_10012]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_3,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
% 4.24/1.10      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
% 4.24/1.10      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 4.24/1.10      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 4.24/1.10      | ~ v1_funct_2(k10_tmap_1(X2,X1,X3,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
% 4.24/1.10      | ~ m1_pre_topc(X0,X2)
% 4.24/1.10      | ~ m1_pre_topc(X3,X2)
% 4.24/1.10      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.24/1.10      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 4.24/1.10      | ~ m1_subset_1(k10_tmap_1(X2,X1,X3,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 4.24/1.10      | ~ v2_pre_topc(X1)
% 4.24/1.10      | ~ v2_pre_topc(X2)
% 4.24/1.10      | ~ l1_pre_topc(X1)
% 4.24/1.10      | ~ l1_pre_topc(X2)
% 4.24/1.10      | v2_struct_0(X2)
% 4.24/1.10      | v2_struct_0(X1)
% 4.24/1.10      | v2_struct_0(X3)
% 4.24/1.10      | v2_struct_0(X0)
% 4.24/1.10      | ~ v1_funct_1(X5)
% 4.24/1.10      | ~ v1_funct_1(X4)
% 4.24/1.10      | ~ v1_funct_1(k10_tmap_1(X2,X1,X3,X0,X4,X5)) ),
% 4.24/1.10      inference(cnf_transformation,[],[f96]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_1324,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53)
% 4.24/1.10      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53))
% 4.24/1.10      | ~ v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.24/1.10      | ~ v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54))
% 4.24/1.10      | ~ v1_funct_2(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54))
% 4.24/1.10      | ~ m1_pre_topc(X3_54,X2_54)
% 4.24/1.10      | ~ m1_pre_topc(X0_54,X2_54)
% 4.24/1.10      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 4.24/1.10      | ~ m1_subset_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54))))
% 4.24/1.10      | ~ v2_pre_topc(X1_54)
% 4.24/1.10      | ~ v2_pre_topc(X2_54)
% 4.24/1.10      | ~ l1_pre_topc(X1_54)
% 4.24/1.10      | ~ l1_pre_topc(X2_54)
% 4.24/1.10      | v2_struct_0(X1_54)
% 4.24/1.10      | v2_struct_0(X0_54)
% 4.24/1.10      | v2_struct_0(X3_54)
% 4.24/1.10      | v2_struct_0(X2_54)
% 4.24/1.10      | ~ v1_funct_1(X0_53)
% 4.24/1.10      | ~ v1_funct_1(X1_53)
% 4.24/1.10      | ~ v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) ),
% 4.24/1.10      inference(subtyping,[status(esa)],[c_3]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2041,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53) = iProver_top
% 4.24/1.10      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53)) != iProver_top
% 4.24/1.10      | v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 4.24/1.10      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 4.24/1.10      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(X2_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X2_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(X1_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2531,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(X0_54),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,k1_tsep_1(X2_54,X3_54,X0_54),X0_54,k10_tmap_1(X2_54,X1_54,X3_54,X0_54,X0_53,X1_53)),X1_53) = iProver_top
% 4.24/1.10      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_54,X3_54,X0_54)),u1_struct_0(X1_54),k3_tmap_1(X2_54,X1_54,X3_54,k2_tsep_1(X2_54,X3_54,X0_54),X0_53),k3_tmap_1(X2_54,X1_54,X0_54,k2_tsep_1(X2_54,X3_54,X0_54),X1_53)) != iProver_top
% 4.24/1.10      | v1_funct_2(X1_53,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(X3_54),u1_struct_0(X1_54)) != iProver_top
% 4.24/1.10      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 4.24/1.10      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 4.24/1.10      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | v2_pre_topc(X2_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X1_54) != iProver_top
% 4.24/1.10      | l1_pre_topc(X2_54) != iProver_top
% 4.24/1.10      | v2_struct_0(X1_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X3_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X2_54) = iProver_top
% 4.24/1.10      | v2_struct_0(X0_54) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(X1_53) != iProver_top ),
% 4.24/1.10      inference(forward_subsumption_resolution,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_2041,c_2045,c_2043,c_2044]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_8634,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
% 4.24/1.10      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK5) = iProver_top
% 4.24/1.10      | v2_struct_0(sK4) = iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top
% 4.24/1.10      | v1_funct_1(sK7) != iProver_top
% 4.24/1.10      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_2052,c_2531]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_2863,plain,
% 4.24/1.10      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_54,X1_54,sK5)),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,X1_54,k2_tsep_1(X0_54,X1_54,sK5),X0_53),k3_tmap_1(X0_54,sK3,sK5,k2_tsep_1(X0_54,X1_54,sK5),sK7))
% 4.24/1.10      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_54,sK3,k1_tsep_1(X0_54,X1_54,sK5),sK5,k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7)),sK7)
% 4.24/1.10      | ~ v1_funct_2(X0_53,u1_struct_0(X1_54),u1_struct_0(sK3))
% 4.24/1.10      | ~ v1_funct_2(k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(X0_54,X1_54,sK5)),u1_struct_0(sK3))
% 4.24/1.10      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.10      | ~ m1_pre_topc(X1_54,X0_54)
% 4.24/1.10      | ~ m1_pre_topc(sK5,X0_54)
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3))))
% 4.24/1.10      | ~ m1_subset_1(k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,sK5)),u1_struct_0(sK3))))
% 4.24/1.10      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.10      | ~ v2_pre_topc(X0_54)
% 4.24/1.10      | ~ v2_pre_topc(sK3)
% 4.24/1.10      | ~ l1_pre_topc(X0_54)
% 4.24/1.10      | ~ l1_pre_topc(sK3)
% 4.24/1.10      | v2_struct_0(X1_54)
% 4.24/1.10      | v2_struct_0(X0_54)
% 4.24/1.10      | v2_struct_0(sK5)
% 4.24/1.10      | v2_struct_0(sK3)
% 4.24/1.10      | ~ v1_funct_1(X0_53)
% 4.24/1.10      | ~ v1_funct_1(k10_tmap_1(X0_54,sK3,X1_54,sK5,X0_53,sK7))
% 4.24/1.10      | ~ v1_funct_1(sK7) ),
% 4.24/1.10      inference(instantiation,[status(thm)],[c_1324]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_3115,plain,
% 4.24/1.10      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X0_54,k2_tsep_1(sK2,X0_54,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,X0_54,sK5),sK7))
% 4.24/1.10      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0_54,sK5),sK5,k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7)),sK7)
% 4.24/1.10      | ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(sK3))
% 4.24/1.10      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))
% 4.24/1.10      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.10      | ~ m1_pre_topc(X0_54,sK2)
% 4.24/1.10      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 4.24/1.10      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_54,sK5)),u1_struct_0(sK3))))
% 4.24/1.10      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.10      | ~ v2_pre_topc(sK3)
% 4.24/1.10      | ~ v2_pre_topc(sK2)
% 4.24/1.10      | ~ l1_pre_topc(sK3)
% 4.24/1.10      | ~ l1_pre_topc(sK2)
% 4.24/1.10      | v2_struct_0(X0_54)
% 4.24/1.10      | v2_struct_0(sK5)
% 4.24/1.10      | v2_struct_0(sK3)
% 4.24/1.10      | v2_struct_0(sK2)
% 4.24/1.10      | ~ v1_funct_1(X0_53)
% 4.24/1.10      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,X0_54,sK5,X0_53,sK7))
% 4.24/1.10      | ~ v1_funct_1(sK7) ),
% 4.24/1.10      inference(instantiation,[status(thm)],[c_2863]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_3916,plain,
% 4.24/1.10      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
% 4.24/1.10      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),sK7)
% 4.24/1.10      | ~ v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.24/1.10      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 4.24/1.10      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 4.24/1.10      | ~ m1_pre_topc(sK5,sK2)
% 4.24/1.10      | ~ m1_pre_topc(sK4,sK2)
% 4.24/1.10      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.24/1.10      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 4.24/1.10      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 4.24/1.10      | ~ v2_pre_topc(sK3)
% 4.24/1.10      | ~ v2_pre_topc(sK2)
% 4.24/1.10      | ~ l1_pre_topc(sK3)
% 4.24/1.10      | ~ l1_pre_topc(sK2)
% 4.24/1.10      | v2_struct_0(sK5)
% 4.24/1.10      | v2_struct_0(sK4)
% 4.24/1.10      | v2_struct_0(sK3)
% 4.24/1.10      | v2_struct_0(sK2)
% 4.24/1.10      | ~ v1_funct_1(X0_53)
% 4.24/1.10      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7))
% 4.24/1.10      | ~ v1_funct_1(sK7) ),
% 4.24/1.10      inference(instantiation,[status(thm)],[c_3115]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_3917,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_53),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 4.24/1.10      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)),sK7) = iProver_top
% 4.24/1.10      | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK5) = iProver_top
% 4.24/1.10      | v2_struct_0(sK4) = iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top
% 4.24/1.10      | v1_funct_1(X0_53) != iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_53,sK7)) != iProver_top
% 4.24/1.10      | v1_funct_1(sK7) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_3916]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_3919,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 4.24/1.10      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
% 4.24/1.10      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK5) = iProver_top
% 4.24/1.10      | v2_struct_0(sK4) = iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 4.24/1.10      | v1_funct_1(sK7) != iProver_top
% 4.24/1.10      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.10      inference(instantiation,[status(thm)],[c_3917]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_8819,plain,
% 4.24/1.10      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_8634,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 4.24/1.10                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_67,c_3576,c_3588,
% 4.24/1.10                 c_3751,c_3919]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_8825,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 4.24/1.10      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 4.24/1.10      | v1_funct_1(sK7) != iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_8819,c_7546]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9000,plain,
% 4.24/1.10      ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_8825,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 4.24/1.10                 c_58,c_59,c_60,c_62,c_63,c_64,c_66,c_3576,c_3588,c_3751]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9001,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top ),
% 4.24/1.10      inference(renaming,[status(thm)],[c_9000]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9006,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 4.24/1.10      | m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK5) = iProver_top
% 4.24/1.10      | v2_struct_0(sK4) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_2049,c_9001]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_9088,plain,
% 4.24/1.10      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_9006,c_49,c_50,c_51,c_55,c_56,c_57,c_58,c_3731]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_10050,plain,
% 4.24/1.10      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 4.24/1.10      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 4.24/1.10      | v5_pre_topc(sK6,sK4,sK3) != iProver_top
% 4.24/1.10      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK3) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK3) != iProver_top
% 4.24/1.10      | v2_struct_0(sK3) = iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 4.24/1.10      | v1_funct_1(sK7) != iProver_top
% 4.24/1.10      | v1_funct_1(sK6) != iProver_top ),
% 4.24/1.10      inference(light_normalisation,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_10034,c_9088,c_9788]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_36,negated_conjecture,
% 4.24/1.10      ( v5_pre_topc(sK6,sK4,sK3) ),
% 4.24/1.10      inference(cnf_transformation,[],[f86]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_61,plain,
% 4.24/1.10      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_32,negated_conjecture,
% 4.24/1.10      ( v5_pre_topc(sK7,sK5,sK3) ),
% 4.24/1.10      inference(cnf_transformation,[],[f90]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_65,plain,
% 4.24/1.10      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_28,negated_conjecture,
% 4.24/1.10      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
% 4.24/1.10      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 4.24/1.10      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 4.24/1.10      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 4.24/1.10      inference(cnf_transformation,[],[f94]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_69,plain,
% 4.24/1.10      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
% 4.24/1.10      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 4.24/1.10      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 4.24/1.10      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 4.24/1.10      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_10107,plain,
% 4.24/1.10      ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top ),
% 4.24/1.10      inference(global_propositional_subsumption,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_10050,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,
% 4.24/1.10                 c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_69,
% 4.24/1.10                 c_3576,c_3588,c_3751]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(c_10112,plain,
% 4.24/1.10      ( m1_pre_topc(sK5,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 4.24/1.10      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.24/1.10      | v2_pre_topc(sK2) != iProver_top
% 4.24/1.10      | l1_pre_topc(sK2) != iProver_top
% 4.24/1.10      | v2_struct_0(sK5) = iProver_top
% 4.24/1.10      | v2_struct_0(sK4) = iProver_top
% 4.24/1.10      | v2_struct_0(sK2) = iProver_top ),
% 4.24/1.10      inference(superposition,[status(thm)],[c_2049,c_10107]) ).
% 4.24/1.10  
% 4.24/1.10  cnf(contradiction,plain,
% 4.24/1.10      ( $false ),
% 4.24/1.10      inference(minisat,
% 4.24/1.10                [status(thm)],
% 4.24/1.10                [c_10112,c_3731,c_58,c_57,c_56,c_55,c_51,c_50,c_49]) ).
% 4.24/1.10  
% 4.24/1.10  
% 4.24/1.10  % SZS output end CNFRefutation for theBenchmark.p
% 4.24/1.10  
% 4.24/1.10  ------                               Statistics
% 4.24/1.10  
% 4.24/1.10  ------ General
% 4.24/1.10  
% 4.24/1.10  abstr_ref_over_cycles:                  0
% 4.24/1.10  abstr_ref_under_cycles:                 0
% 4.24/1.10  gc_basic_clause_elim:                   0
% 4.24/1.10  forced_gc_time:                         0
% 4.24/1.10  parsing_time:                           0.014
% 4.24/1.10  unif_index_cands_time:                  0.
% 4.24/1.10  unif_index_add_time:                    0.
% 4.24/1.10  orderings_time:                         0.
% 4.24/1.10  out_proof_time:                         0.024
% 4.24/1.10  total_time:                             0.55
% 4.24/1.10  num_of_symbols:                         58
% 4.24/1.10  num_of_terms:                           17351
% 4.24/1.10  
% 4.24/1.10  ------ Preprocessing
% 4.24/1.10  
% 4.24/1.10  num_of_splits:                          0
% 4.24/1.10  num_of_split_atoms:                     0
% 4.24/1.10  num_of_reused_defs:                     0
% 4.24/1.10  num_eq_ax_congr_red:                    40
% 4.24/1.10  num_of_sem_filtered_clauses:            1
% 4.24/1.10  num_of_subtypes:                        5
% 4.24/1.10  monotx_restored_types:                  0
% 4.24/1.10  sat_num_of_epr_types:                   0
% 4.24/1.10  sat_num_of_non_cyclic_types:            0
% 4.24/1.10  sat_guarded_non_collapsed_types:        1
% 4.24/1.10  num_pure_diseq_elim:                    0
% 4.24/1.10  simp_replaced_by:                       0
% 4.24/1.10  res_preprocessed:                       194
% 4.24/1.10  prep_upred:                             0
% 4.24/1.10  prep_unflattend:                        73
% 4.24/1.10  smt_new_axioms:                         0
% 4.24/1.10  pred_elim_cands:                        9
% 4.24/1.10  pred_elim:                              3
% 4.24/1.10  pred_elim_cl:                           7
% 4.24/1.10  pred_elim_cycles:                       5
% 4.24/1.10  merged_defs:                            0
% 4.24/1.10  merged_defs_ncl:                        0
% 4.24/1.10  bin_hyper_res:                          0
% 4.24/1.10  prep_cycles:                            4
% 4.24/1.10  pred_elim_time:                         0.023
% 4.24/1.10  splitting_time:                         0.
% 4.24/1.10  sem_filter_time:                        0.
% 4.24/1.10  monotx_time:                            0.
% 4.24/1.10  subtype_inf_time:                       0.002
% 4.24/1.10  
% 4.24/1.10  ------ Problem properties
% 4.24/1.10  
% 4.24/1.10  clauses:                                42
% 4.24/1.10  conjectures:                            20
% 4.24/1.10  epr:                                    15
% 4.24/1.10  horn:                                   23
% 4.24/1.10  ground:                                 20
% 4.24/1.10  unary:                                  19
% 4.24/1.10  binary:                                 1
% 4.24/1.10  lits:                                   280
% 4.24/1.10  lits_eq:                                2
% 4.24/1.10  fd_pure:                                0
% 4.24/1.10  fd_pseudo:                              0
% 4.24/1.10  fd_cond:                                0
% 4.24/1.10  fd_pseudo_cond:                         2
% 4.24/1.10  ac_symbols:                             0
% 4.24/1.10  
% 4.24/1.10  ------ Propositional Solver
% 4.24/1.10  
% 4.24/1.10  prop_solver_calls:                      27
% 4.24/1.10  prop_fast_solver_calls:                 3978
% 4.24/1.10  smt_solver_calls:                       0
% 4.24/1.10  smt_fast_solver_calls:                  0
% 4.24/1.10  prop_num_of_clauses:                    3080
% 4.24/1.10  prop_preprocess_simplified:             8953
% 4.24/1.10  prop_fo_subsumed:                       280
% 4.24/1.10  prop_solver_time:                       0.
% 4.24/1.10  smt_solver_time:                        0.
% 4.24/1.10  smt_fast_solver_time:                   0.
% 4.24/1.10  prop_fast_solver_time:                  0.
% 4.24/1.10  prop_unsat_core_time:                   0.
% 4.24/1.10  
% 4.24/1.10  ------ QBF
% 4.24/1.10  
% 4.24/1.10  qbf_q_res:                              0
% 4.24/1.10  qbf_num_tautologies:                    0
% 4.24/1.10  qbf_prep_cycles:                        0
% 4.24/1.10  
% 4.24/1.10  ------ BMC1
% 4.24/1.10  
% 4.24/1.10  bmc1_current_bound:                     -1
% 4.24/1.10  bmc1_last_solved_bound:                 -1
% 4.24/1.10  bmc1_unsat_core_size:                   -1
% 4.24/1.10  bmc1_unsat_core_parents_size:           -1
% 4.24/1.10  bmc1_merge_next_fun:                    0
% 4.24/1.10  bmc1_unsat_core_clauses_time:           0.
% 4.24/1.10  
% 4.24/1.10  ------ Instantiation
% 4.24/1.10  
% 4.24/1.10  inst_num_of_clauses:                    863
% 4.24/1.10  inst_num_in_passive:                    8
% 4.24/1.10  inst_num_in_active:                     459
% 4.24/1.10  inst_num_in_unprocessed:                396
% 4.24/1.10  inst_num_of_loops:                      480
% 4.24/1.10  inst_num_of_learning_restarts:          0
% 4.24/1.10  inst_num_moves_active_passive:          18
% 4.24/1.10  inst_lit_activity:                      0
% 4.24/1.10  inst_lit_activity_moves:                0
% 4.24/1.10  inst_num_tautologies:                   0
% 4.24/1.10  inst_num_prop_implied:                  0
% 4.24/1.10  inst_num_existing_simplified:           0
% 4.24/1.10  inst_num_eq_res_simplified:             0
% 4.24/1.10  inst_num_child_elim:                    0
% 4.24/1.10  inst_num_of_dismatching_blockings:      192
% 4.24/1.10  inst_num_of_non_proper_insts:           812
% 4.24/1.10  inst_num_of_duplicates:                 0
% 4.24/1.10  inst_inst_num_from_inst_to_res:         0
% 4.24/1.10  inst_dismatching_checking_time:         0.
% 4.24/1.10  
% 4.24/1.10  ------ Resolution
% 4.24/1.10  
% 4.24/1.10  res_num_of_clauses:                     0
% 4.24/1.10  res_num_in_passive:                     0
% 4.24/1.10  res_num_in_active:                      0
% 4.24/1.10  res_num_of_loops:                       198
% 4.24/1.10  res_forward_subset_subsumed:            25
% 4.24/1.10  res_backward_subset_subsumed:           0
% 4.24/1.10  res_forward_subsumed:                   0
% 4.24/1.10  res_backward_subsumed:                  0
% 4.24/1.10  res_forward_subsumption_resolution:     0
% 4.24/1.10  res_backward_subsumption_resolution:    0
% 4.24/1.10  res_clause_to_clause_subsumption:       925
% 4.24/1.10  res_orphan_elimination:                 0
% 4.24/1.10  res_tautology_del:                      72
% 4.24/1.10  res_num_eq_res_simplified:              0
% 4.24/1.10  res_num_sel_changes:                    0
% 4.24/1.10  res_moves_from_active_to_pass:          0
% 4.24/1.10  
% 4.24/1.10  ------ Superposition
% 4.24/1.10  
% 4.24/1.10  sup_time_total:                         0.
% 4.24/1.10  sup_time_generating:                    0.
% 4.24/1.10  sup_time_sim_full:                      0.
% 4.24/1.10  sup_time_sim_immed:                     0.
% 4.24/1.10  
% 4.24/1.10  sup_num_of_clauses:                     103
% 4.24/1.10  sup_num_in_active:                      90
% 4.24/1.10  sup_num_in_passive:                     13
% 4.24/1.10  sup_num_of_loops:                       95
% 4.24/1.10  sup_fw_superposition:                   47
% 4.24/1.10  sup_bw_superposition:                   73
% 4.24/1.10  sup_immediate_simplified:               40
% 4.24/1.10  sup_given_eliminated:                   0
% 4.24/1.10  comparisons_done:                       0
% 4.24/1.10  comparisons_avoided:                    0
% 4.24/1.10  
% 4.24/1.10  ------ Simplifications
% 4.24/1.10  
% 4.24/1.10  
% 4.24/1.10  sim_fw_subset_subsumed:                 30
% 4.24/1.10  sim_bw_subset_subsumed:                 4
% 4.24/1.10  sim_fw_subsumed:                        8
% 4.24/1.10  sim_bw_subsumed:                        0
% 4.24/1.10  sim_fw_subsumption_res:                 16
% 4.24/1.10  sim_bw_subsumption_res:                 0
% 4.24/1.10  sim_tautology_del:                      3
% 4.24/1.10  sim_eq_tautology_del:                   7
% 4.24/1.10  sim_eq_res_simp:                        0
% 4.24/1.10  sim_fw_demodulated:                     2
% 4.24/1.10  sim_bw_demodulated:                     2
% 4.24/1.10  sim_light_normalised:                   6
% 4.24/1.10  sim_joinable_taut:                      0
% 4.24/1.10  sim_joinable_simp:                      0
% 4.24/1.10  sim_ac_normalised:                      0
% 4.24/1.10  sim_smt_subsumption:                    0
% 4.24/1.10  
%------------------------------------------------------------------------------
