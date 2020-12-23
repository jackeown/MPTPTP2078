%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:28 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 615 expanded)
%              Number of clauses        :  116 ( 145 expanded)
%              Number of leaves         :   30 ( 276 expanded)
%              Depth                    :   18
%              Number of atoms          : 1117 (8475 expanded)
%              Number of equality atoms :  215 (1226 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK5)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X3,X1,X4,X5)
                  & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X3,X1,sK4,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,X1,X4,X5)
                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK3,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,X1,X4,X5)
                          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,X1,X4,X5)
                        & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,sK1,X4,X5)
                            & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f53,f52,f51,f50,f49,f48,f47])).

fof(f83,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f39])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f75])).

fof(f87,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f94,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_972,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2412,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_3038,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_3933,plain,
    ( k2_struct_0(X0) != u1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3038])).

cnf(c_8062,plain,
    ( k2_struct_0(X0) != u1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3933])).

cnf(c_10427,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK2)
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8062])).

cnf(c_1951,plain,
    ( u1_struct_0(X0) != X1
    | u1_struct_0(X0) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_2120,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_3180,plain,
    ( u1_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(X0) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_2120])).

cnf(c_6510,plain,
    ( u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(sK2) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_3180])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3485,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
    | m1_pre_topc(sK2,X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5760,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3485])).

cnf(c_2860,plain,
    ( X0 != X1
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_3736,plain,
    ( X0 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2860])).

cnf(c_4849,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3736])).

cnf(c_979,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2139,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X3 != X1
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_2548,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
    | ~ m1_pre_topc(sK3,X1)
    | X0 != X1
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3324,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
    | ~ m1_pre_topc(sK3,sK3)
    | X0 != sK3
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_4201,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3324])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3445,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_32])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3443,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_30])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3359,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3325,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_16,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_215,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_216,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_446,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k2_struct_0(X2) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_216])).

cnf(c_447,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_542,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_543,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_547,plain,
    ( ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_29])).

cnf(c_548,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_547])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_591,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_548,c_18])).

cnf(c_613,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | k2_struct_0(X6) != u1_struct_0(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_447,c_591])).

cnf(c_614,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_struct_0(X3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_658,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_614,c_4,c_1])).

cnf(c_1904,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
    | r1_tmap_1(sK3,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(sK3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_2125,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),sK5)
    | r1_tmap_1(sK3,X1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(sK3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_3189,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(sK3) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1596,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2992,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1596])).

cnf(c_2119,plain,
    ( X0 != X1
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_2325,plain,
    ( X0 != u1_struct_0(sK3)
    | u1_struct_0(sK3) = X0
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2119])).

cnf(c_2968,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2325])).

cnf(c_976,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2909,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_976,c_26])).

cnf(c_2910,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2909])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1958,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | X1 = u1_struct_0(X0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2824,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_978,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2807,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_978,c_26])).

cnf(c_971,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2626,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1946,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2541,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_2542,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2541])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_409,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_2265,plain,
    ( ~ l1_pre_topc(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_2216,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_977,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2007,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X0 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_2173,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_2174,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_2161,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

cnf(c_2162,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_2159,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_30])).

cnf(c_2160,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2159])).

cnf(c_973,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1930,plain,
    ( X0 != sK3
    | u1_struct_0(X0) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_2114,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1930])).

cnf(c_1903,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1586,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1625,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1586,c_23])).

cnf(c_1822,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1625])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1587,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1642,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1587,c_23])).

cnf(c_1815,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1642])).

cnf(c_1000,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_986,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10427,c_6510,c_5760,c_4849,c_4201,c_3445,c_3443,c_3359,c_3325,c_3189,c_2992,c_2968,c_2910,c_2824,c_2807,c_2626,c_2542,c_2265,c_2216,c_2174,c_2173,c_2162,c_2161,c_2160,c_2159,c_2114,c_1903,c_1822,c_1815,c_1000,c_986,c_21,c_25,c_26,c_27,c_30,c_31,c_46,c_33,c_34,c_35,c_36,c_42,c_37,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:47:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.31/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/0.99  
% 3.31/0.99  ------  iProver source info
% 3.31/0.99  
% 3.31/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.31/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/0.99  git: non_committed_changes: false
% 3.31/0.99  git: last_make_outside_of_git: false
% 3.31/0.99  
% 3.31/0.99  ------ 
% 3.31/0.99  ------ Parsing...
% 3.31/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/0.99  ------ Proving...
% 3.31/0.99  ------ Problem Properties 
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  clauses                                 33
% 3.31/0.99  conjectures                             17
% 3.31/0.99  EPR                                     16
% 3.31/0.99  Horn                                    30
% 3.31/0.99  unary                                   17
% 3.31/0.99  binary                                  3
% 3.31/0.99  lits                                    102
% 3.31/0.99  lits eq                                 14
% 3.31/0.99  fd_pure                                 0
% 3.31/0.99  fd_pseudo                               0
% 3.31/0.99  fd_cond                                 0
% 3.31/0.99  fd_pseudo_cond                          2
% 3.31/0.99  AC symbols                              0
% 3.31/0.99  
% 3.31/0.99  ------ Input Options Time Limit: Unbounded
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  ------ 
% 3.31/0.99  Current options:
% 3.31/0.99  ------ 
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  ------ Proving...
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  % SZS status Theorem for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  fof(f10,axiom,(
% 3.31/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f31,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f10])).
% 3.31/0.99  
% 3.31/0.99  fof(f32,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(flattening,[],[f31])).
% 3.31/0.99  
% 3.31/0.99  fof(f43,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(nnf_transformation,[],[f32])).
% 3.31/0.99  
% 3.31/0.99  fof(f66,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f43])).
% 3.31/0.99  
% 3.31/0.99  fof(f96,plain,(
% 3.31/0.99    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(equality_resolution,[],[f66])).
% 3.31/0.99  
% 3.31/0.99  fof(f2,axiom,(
% 3.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f20,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/0.99    inference(ennf_transformation,[],[f2])).
% 3.31/0.99  
% 3.31/0.99  fof(f21,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/0.99    inference(flattening,[],[f20])).
% 3.31/0.99  
% 3.31/0.99  fof(f56,plain,(
% 3.31/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f21])).
% 3.31/0.99  
% 3.31/0.99  fof(f16,conjecture,(
% 3.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f17,negated_conjecture,(
% 3.31/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.31/0.99    inference(negated_conjecture,[],[f16])).
% 3.31/0.99  
% 3.31/0.99  fof(f41,plain,(
% 3.31/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.31/0.99    inference(ennf_transformation,[],[f17])).
% 3.31/0.99  
% 3.31/0.99  fof(f42,plain,(
% 3.31/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.31/0.99    inference(flattening,[],[f41])).
% 3.31/0.99  
% 3.31/0.99  fof(f53,plain,(
% 3.31/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f52,plain,(
% 3.31/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f51,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f50,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f49,plain,(
% 3.31/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f48,plain,(
% 3.31/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f47,plain,(
% 3.31/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f54,plain,(
% 3.31/0.99    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f53,f52,f51,f50,f49,f48,f47])).
% 3.31/0.99  
% 3.31/0.99  fof(f83,plain,(
% 3.31/0.99    m1_pre_topc(sK2,sK0)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f85,plain,(
% 3.31/0.99    m1_pre_topc(sK3,sK0)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f6,axiom,(
% 3.31/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f25,plain,(
% 3.31/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f6])).
% 3.31/0.99  
% 3.31/0.99  fof(f60,plain,(
% 3.31/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f25])).
% 3.31/0.99  
% 3.31/0.99  fof(f13,axiom,(
% 3.31/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f36,plain,(
% 3.31/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f13])).
% 3.31/0.99  
% 3.31/0.99  fof(f72,plain,(
% 3.31/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f36])).
% 3.31/0.99  
% 3.31/0.99  fof(f9,axiom,(
% 3.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f29,plain,(
% 3.31/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/0.99    inference(ennf_transformation,[],[f9])).
% 3.31/0.99  
% 3.31/0.99  fof(f30,plain,(
% 3.31/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/0.99    inference(flattening,[],[f29])).
% 3.31/0.99  
% 3.31/0.99  fof(f65,plain,(
% 3.31/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f30])).
% 3.31/0.99  
% 3.31/0.99  fof(f11,axiom,(
% 3.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f33,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/0.99    inference(ennf_transformation,[],[f11])).
% 3.31/0.99  
% 3.31/0.99  fof(f34,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/0.99    inference(flattening,[],[f33])).
% 3.31/0.99  
% 3.31/0.99  fof(f44,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/0.99    inference(nnf_transformation,[],[f34])).
% 3.31/0.99  
% 3.31/0.99  fof(f45,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/0.99    inference(flattening,[],[f44])).
% 3.31/0.99  
% 3.31/0.99  fof(f69,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f45])).
% 3.31/0.99  
% 3.31/0.99  fof(f98,plain,(
% 3.31/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/0.99    inference(equality_resolution,[],[f69])).
% 3.31/0.99  
% 3.31/0.99  fof(f12,axiom,(
% 3.31/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f35,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f12])).
% 3.31/0.99  
% 3.31/0.99  fof(f71,plain,(
% 3.31/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f35])).
% 3.31/0.99  
% 3.31/0.99  fof(f15,axiom,(
% 3.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f39,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/0.99    inference(ennf_transformation,[],[f15])).
% 3.31/0.99  
% 3.31/0.99  fof(f40,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/0.99    inference(flattening,[],[f39])).
% 3.31/0.99  
% 3.31/0.99  fof(f46,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/0.99    inference(nnf_transformation,[],[f40])).
% 3.31/0.99  
% 3.31/0.99  fof(f75,plain,(
% 3.31/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f46])).
% 3.31/0.99  
% 3.31/0.99  fof(f100,plain,(
% 3.31/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/0.99    inference(equality_resolution,[],[f75])).
% 3.31/0.99  
% 3.31/0.99  fof(f87,plain,(
% 3.31/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f86,plain,(
% 3.31/0.99    v1_funct_1(sK4)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f14,axiom,(
% 3.31/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f37,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/0.99    inference(ennf_transformation,[],[f14])).
% 3.31/0.99  
% 3.31/0.99  fof(f38,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/0.99    inference(flattening,[],[f37])).
% 3.31/0.99  
% 3.31/0.99  fof(f73,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f38])).
% 3.31/0.99  
% 3.31/0.99  fof(f5,axiom,(
% 3.31/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f24,plain,(
% 3.31/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f5])).
% 3.31/0.99  
% 3.31/0.99  fof(f59,plain,(
% 3.31/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f24])).
% 3.31/0.99  
% 3.31/0.99  fof(f89,plain,(
% 3.31/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f7,axiom,(
% 3.31/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f26,plain,(
% 3.31/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/0.99    inference(ennf_transformation,[],[f7])).
% 3.31/0.99  
% 3.31/0.99  fof(f27,plain,(
% 3.31/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/0.99    inference(flattening,[],[f26])).
% 3.31/0.99  
% 3.31/0.99  fof(f62,plain,(
% 3.31/0.99    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f27])).
% 3.31/0.99  
% 3.31/0.99  fof(f8,axiom,(
% 3.31/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f28,plain,(
% 3.31/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.31/0.99    inference(ennf_transformation,[],[f8])).
% 3.31/0.99  
% 3.31/0.99  fof(f63,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f28])).
% 3.31/0.99  
% 3.31/0.99  fof(f1,axiom,(
% 3.31/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f18,plain,(
% 3.31/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f1])).
% 3.31/0.99  
% 3.31/0.99  fof(f19,plain,(
% 3.31/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(flattening,[],[f18])).
% 3.31/0.99  
% 3.31/0.99  fof(f55,plain,(
% 3.31/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f19])).
% 3.31/0.99  
% 3.31/0.99  fof(f4,axiom,(
% 3.31/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f23,plain,(
% 3.31/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f4])).
% 3.31/0.99  
% 3.31/0.99  fof(f58,plain,(
% 3.31/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f23])).
% 3.31/0.99  
% 3.31/0.99  fof(f3,axiom,(
% 3.31/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f22,plain,(
% 3.31/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.31/0.99    inference(ennf_transformation,[],[f3])).
% 3.31/0.99  
% 3.31/0.99  fof(f57,plain,(
% 3.31/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f22])).
% 3.31/0.99  
% 3.31/0.99  fof(f91,plain,(
% 3.31/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f92,plain,(
% 3.31/0.99    sK5 = sK6),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f93,plain,(
% 3.31/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f94,plain,(
% 3.31/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f90,plain,(
% 3.31/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f88,plain,(
% 3.31/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f84,plain,(
% 3.31/0.99    ~v2_struct_0(sK3)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f82,plain,(
% 3.31/0.99    ~v2_struct_0(sK2)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f81,plain,(
% 3.31/0.99    l1_pre_topc(sK1)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f80,plain,(
% 3.31/0.99    v2_pre_topc(sK1)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f79,plain,(
% 3.31/0.99    ~v2_struct_0(sK1)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f78,plain,(
% 3.31/0.99    l1_pre_topc(sK0)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f77,plain,(
% 3.31/0.99    v2_pre_topc(sK0)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f76,plain,(
% 3.31/0.99    ~v2_struct_0(sK0)),
% 3.31/0.99    inference(cnf_transformation,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  cnf(c_972,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2412,plain,
% 3.31/0.99      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3038,plain,
% 3.31/0.99      ( X0 != u1_struct_0(X1)
% 3.31/0.99      | X0 = u1_struct_0(X2)
% 3.31/0.99      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2412]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3933,plain,
% 3.31/0.99      ( k2_struct_0(X0) != u1_struct_0(X0)
% 3.31/0.99      | k2_struct_0(X0) = u1_struct_0(X1)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(X0) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_3038]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_8062,plain,
% 3.31/0.99      ( k2_struct_0(X0) != u1_struct_0(X0)
% 3.31/0.99      | k2_struct_0(X0) = u1_struct_0(sK2)
% 3.31/0.99      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_3933]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_10427,plain,
% 3.31/0.99      ( k2_struct_0(sK3) = u1_struct_0(sK2)
% 3.31/0.99      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 3.31/0.99      | u1_struct_0(sK2) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_8062]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1951,plain,
% 3.31/0.99      ( u1_struct_0(X0) != X1
% 3.31/0.99      | u1_struct_0(X0) = u1_struct_0(sK3)
% 3.31/0.99      | u1_struct_0(sK3) != X1 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2120,plain,
% 3.31/0.99      ( u1_struct_0(X0) != u1_struct_0(X1)
% 3.31/0.99      | u1_struct_0(X0) = u1_struct_0(sK3)
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(X1) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1951]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3180,plain,
% 3.31/0.99      ( u1_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | u1_struct_0(X0) = u1_struct_0(sK3)
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2120]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6510,plain,
% 3.31/0.99      ( u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | u1_struct_0(sK2) = u1_struct_0(sK3)
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_3180]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_12,plain,
% 3.31/0.99      ( m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.31/0.99      | ~ v2_pre_topc(X0)
% 3.31/0.99      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X0)
% 3.31/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.31/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3485,plain,
% 3.31/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
% 3.31/0.99      | m1_pre_topc(sK2,X0)
% 3.31/0.99      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ v2_pre_topc(sK2)
% 3.31/0.99      | ~ l1_pre_topc(X0)
% 3.31/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ l1_pre_topc(sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5760,plain,
% 3.31/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.31/0.99      | m1_pre_topc(sK2,sK3)
% 3.31/0.99      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ v2_pre_topc(sK2)
% 3.31/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ l1_pre_topc(sK2)
% 3.31/0.99      | ~ l1_pre_topc(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_3485]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2860,plain,
% 3.31/0.99      ( X0 != X1 | u1_struct_0(sK2) != X1 | u1_struct_0(sK2) = X0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3736,plain,
% 3.31/0.99      ( X0 != u1_struct_0(sK2)
% 3.31/0.99      | u1_struct_0(sK2) = X0
% 3.31/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2860]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4849,plain,
% 3.31/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK2)
% 3.31/0.99      | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_3736]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_979,plain,
% 3.31/0.99      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.31/0.99      theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2139,plain,
% 3.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
% 3.31/0.99      | X3 != X1
% 3.31/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_979]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2548,plain,
% 3.31/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
% 3.31/0.99      | ~ m1_pre_topc(sK3,X1)
% 3.31/0.99      | X0 != X1
% 3.31/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2139]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3324,plain,
% 3.31/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0)
% 3.31/0.99      | ~ m1_pre_topc(sK3,sK3)
% 3.31/0.99      | X0 != sK3
% 3.31/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2548]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4201,plain,
% 3.31/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.31/0.99      | ~ m1_pre_topc(sK3,sK3)
% 3.31/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 3.31/0.99      | sK3 != sK3 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_3324]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1,plain,
% 3.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | v2_pre_topc(X0)
% 3.31/0.99      | ~ l1_pre_topc(X1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_32,negated_conjecture,
% 3.31/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3445,plain,
% 3.31/0.99      ( ~ v2_pre_topc(sK0) | v2_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_1,c_32]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_30,negated_conjecture,
% 3.31/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3443,plain,
% 3.31/0.99      ( ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_1,c_30]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5,plain,
% 3.31/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.31/0.99      | ~ l1_pre_topc(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3359,plain,
% 3.31/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.31/0.99      | ~ l1_pre_topc(sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_17,plain,
% 3.31/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3325,plain,
% 3.31/0.99      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_10,plain,
% 3.31/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.31/0.99      | ~ v2_pre_topc(X0)
% 3.31/0.99      | ~ l1_pre_topc(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_14,plain,
% 3.31/0.99      ( v1_tsep_1(X0,X1)
% 3.31/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.31/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/0.99      | ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_16,plain,
% 3.31/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/0.99      | ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ l1_pre_topc(X1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_215,plain,
% 3.31/0.99      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.31/0.99      | v1_tsep_1(X0,X1)
% 3.31/0.99      | ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X1) ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_14,c_16]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_216,plain,
% 3.31/0.99      ( v1_tsep_1(X0,X1)
% 3.31/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.31/0.99      | ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X1) ),
% 3.31/0.99      inference(renaming,[status(thm)],[c_215]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_446,plain,
% 3.31/0.99      ( v1_tsep_1(X0,X1)
% 3.31/0.99      | ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | X1 != X2
% 3.31/0.99      | k2_struct_0(X2) != u1_struct_0(X0) ),
% 3.31/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_216]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_447,plain,
% 3.31/0.99      ( v1_tsep_1(X0,X1)
% 3.31/0.99      | ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | k2_struct_0(X1) != u1_struct_0(X0) ),
% 3.31/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_19,plain,
% 3.31/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.31/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.31/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/0.99      | ~ v1_tsep_1(X4,X0)
% 3.31/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_pre_topc(X4,X5)
% 3.31/0.99      | ~ m1_pre_topc(X0,X5)
% 3.31/0.99      | ~ m1_pre_topc(X4,X0)
% 3.31/0.99      | ~ v1_funct_1(X2)
% 3.31/0.99      | v2_struct_0(X5)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X4)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | ~ v2_pre_topc(X5)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X5)
% 3.31/0.99      | ~ l1_pre_topc(X1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_28,negated_conjecture,
% 3.31/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_542,plain,
% 3.31/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.31/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.31/0.99      | ~ v1_tsep_1(X4,X0)
% 3.31/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_pre_topc(X4,X5)
% 3.31/0.99      | ~ m1_pre_topc(X0,X5)
% 3.31/0.99      | ~ m1_pre_topc(X4,X0)
% 3.31/0.99      | ~ v1_funct_1(X2)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X5)
% 3.31/0.99      | v2_struct_0(X4)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X5)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X5)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.31/0.99      | sK4 != X2 ),
% 3.31/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_543,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/0.99      | ~ v1_tsep_1(X0,X3)
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X0,X2)
% 3.31/0.99      | ~ m1_pre_topc(X3,X2)
% 3.31/0.99      | ~ m1_pre_topc(X0,X3)
% 3.31/0.99      | ~ v1_funct_1(sK4)
% 3.31/0.99      | v2_struct_0(X3)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(unflattening,[status(thm)],[c_542]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_29,negated_conjecture,
% 3.31/0.99      ( v1_funct_1(sK4) ),
% 3.31/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_547,plain,
% 3.31/0.99      ( ~ m1_pre_topc(X0,X3)
% 3.31/0.99      | ~ m1_pre_topc(X3,X2)
% 3.31/0.99      | ~ m1_pre_topc(X0,X2)
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/0.99      | ~ v1_tsep_1(X0,X3)
% 3.31/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/0.99      | v2_struct_0(X3)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_543,c_29]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_548,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/0.99      | ~ v1_tsep_1(X0,X3)
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X3,X2)
% 3.31/0.99      | ~ m1_pre_topc(X0,X2)
% 3.31/0.99      | ~ m1_pre_topc(X0,X3)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X3)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(renaming,[status(thm)],[c_547]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_18,plain,
% 3.31/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.31/0.99      | ~ m1_pre_topc(X2,X0)
% 3.31/0.99      | m1_pre_topc(X2,X1)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_591,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/0.99      | ~ v1_tsep_1(X0,X3)
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X3,X2)
% 3.31/0.99      | ~ m1_pre_topc(X0,X3)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X3)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(forward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_548,c_18]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_613,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X5,X6)
% 3.31/0.99      | ~ m1_pre_topc(X0,X3)
% 3.31/0.99      | ~ m1_pre_topc(X3,X2)
% 3.31/0.99      | v2_struct_0(X3)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | ~ v2_pre_topc(X6)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X6)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | X0 != X5
% 3.31/0.99      | X3 != X6
% 3.31/0.99      | k2_struct_0(X6) != u1_struct_0(X5)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(resolution_lifted,[status(thm)],[c_447,c_591]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_614,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X0,X3)
% 3.31/0.99      | ~ m1_pre_topc(X3,X2)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X3)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ v2_pre_topc(X3)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X3)
% 3.31/0.99      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(unflattening,[status(thm)],[c_613]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4,plain,
% 3.31/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_658,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X3,X2)
% 3.31/0.99      | ~ m1_pre_topc(X0,X3)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X3)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(forward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_614,c_4,c_1]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1904,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 3.31/0.99      | r1_tmap_1(sK3,X1,sK4,X3)
% 3.31/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X0,sK3)
% 3.31/0.99      | ~ m1_pre_topc(sK3,X2)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | v2_struct_0(sK3)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | k2_struct_0(sK3) != u1_struct_0(X0)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2125,plain,
% 3.31/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),sK5)
% 3.31/0.99      | r1_tmap_1(sK3,X1,sK4,sK5)
% 3.31/0.99      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 3.31/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 3.31/0.99      | ~ m1_pre_topc(X0,sK3)
% 3.31/0.99      | ~ m1_pre_topc(sK3,X2)
% 3.31/0.99      | v2_struct_0(X0)
% 3.31/0.99      | v2_struct_0(X1)
% 3.31/0.99      | v2_struct_0(X2)
% 3.31/0.99      | v2_struct_0(sK3)
% 3.31/0.99      | ~ v2_pre_topc(X1)
% 3.31/0.99      | ~ v2_pre_topc(X2)
% 3.31/0.99      | ~ l1_pre_topc(X1)
% 3.31/0.99      | ~ l1_pre_topc(X2)
% 3.31/0.99      | k2_struct_0(sK3) != u1_struct_0(X0)
% 3.31/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1904]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3189,plain,
% 3.31/0.99      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 3.31/0.99      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.31/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.31/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.31/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.31/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.31/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.31/0.99      | v2_struct_0(sK0)
% 3.31/0.99      | v2_struct_0(sK2)
% 3.31/0.99      | v2_struct_0(sK1)
% 3.31/0.99      | v2_struct_0(sK3)
% 3.31/0.99      | ~ v2_pre_topc(sK0)
% 3.31/0.99      | ~ v2_pre_topc(sK1)
% 3.31/0.99      | ~ l1_pre_topc(sK0)
% 3.31/0.99      | ~ l1_pre_topc(sK1)
% 3.31/0.99      | k2_struct_0(sK3) != u1_struct_0(sK2)
% 3.31/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2125]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_26,negated_conjecture,
% 3.31/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.31/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6,plain,
% 3.31/0.99      ( v2_struct_0(X0)
% 3.31/0.99      | ~ l1_pre_topc(X0)
% 3.31/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.31/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1596,plain,
% 3.31/0.99      ( v2_struct_0(X0) = iProver_top
% 3.31/0.99      | l1_pre_topc(X0) != iProver_top
% 3.31/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2992,plain,
% 3.31/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.31/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.31/0.99      | v1_pre_topc(sK3) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_26,c_1596]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2119,plain,
% 3.31/0.99      ( X0 != X1 | u1_struct_0(sK3) != X1 | u1_struct_0(sK3) = X0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2325,plain,
% 3.31/0.99      ( X0 != u1_struct_0(sK3)
% 3.31/0.99      | u1_struct_0(sK3) = X0
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2119]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2968,plain,
% 3.31/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK3)
% 3.31/0.99      | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2325]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_976,plain,
% 3.31/0.99      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 3.31/0.99      theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2909,plain,
% 3.31/0.99      ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ v1_pre_topc(sK3) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_976,c_26]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2910,plain,
% 3.31/0.99      ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.31/0.99      | v1_pre_topc(sK3) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2909]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_9,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.31/0.99      | X2 = X1
% 3.31/0.99      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1958,plain,
% 3.31/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.31/0.99      | X1 = u1_struct_0(X0)
% 3.31/0.99      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2824,plain,
% 3.31/0.99      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.31/0.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.31/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1958]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_978,plain,
% 3.31/0.99      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 3.31/0.99      theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2807,plain,
% 3.31/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ v2_pre_topc(sK3) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_978,c_26]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_971,plain,( X0 = X0 ),theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2626,plain,
% 3.31/0.99      ( sK3 = sK3 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_971]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_0,plain,
% 3.31/0.99      ( ~ l1_pre_topc(X0)
% 3.31/0.99      | ~ v1_pre_topc(X0)
% 3.31/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1946,plain,
% 3.31/0.99      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.31/0.99      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.31/0.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2541,plain,
% 3.31/0.99      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1946]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2542,plain,
% 3.31/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.31/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.31/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2541]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3,plain,
% 3.31/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2,plain,
% 3.31/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_409,plain,
% 3.31/0.99      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2265,plain,
% 3.31/0.99      ( ~ l1_pre_topc(sK3) | k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_409]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2216,plain,
% 3.31/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_971]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_977,plain,
% 3.31/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 3.31/0.99      theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2007,plain,
% 3.31/0.99      ( ~ l1_pre_topc(X0)
% 3.31/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.31/0.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_977]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2173,plain,
% 3.31/0.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.31/0.99      | ~ l1_pre_topc(sK3)
% 3.31/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2007]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2174,plain,
% 3.31/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 3.31/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.31/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2161,plain,
% 3.31/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_4,c_32]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2162,plain,
% 3.31/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.31/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2159,plain,
% 3.31/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_4,c_30]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2160,plain,
% 3.31/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.31/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2159]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_973,plain,
% 3.31/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.31/0.99      theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1930,plain,
% 3.31/0.99      ( X0 != sK3 | u1_struct_0(X0) = u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_973]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2114,plain,
% 3.31/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 3.31/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1930]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1903,plain,
% 3.31/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_971]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_24,negated_conjecture,
% 3.31/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1586,plain,
% 3.31/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_23,negated_conjecture,
% 3.31/0.99      ( sK5 = sK6 ),
% 3.31/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1625,plain,
% 3.31/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.31/0.99      inference(light_normalisation,[status(thm)],[c_1586,c_23]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1822,plain,
% 3.31/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 3.31/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1625]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_22,negated_conjecture,
% 3.31/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.31/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1587,plain,
% 3.31/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1642,plain,
% 3.31/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.31/0.99      inference(light_normalisation,[status(thm)],[c_1587,c_23]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1815,plain,
% 3.31/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 3.31/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1642]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1000,plain,
% 3.31/0.99      ( sK1 = sK1 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_971]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_986,plain,
% 3.31/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_973]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_21,negated_conjecture,
% 3.31/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.31/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_25,negated_conjecture,
% 3.31/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_27,negated_conjecture,
% 3.31/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.31/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_31,negated_conjecture,
% 3.31/0.99      ( ~ v2_struct_0(sK3) ),
% 3.31/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_33,negated_conjecture,
% 3.31/0.99      ( ~ v2_struct_0(sK2) ),
% 3.31/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_46,plain,
% 3.31/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_34,negated_conjecture,
% 3.31/0.99      ( l1_pre_topc(sK1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_35,negated_conjecture,
% 3.31/0.99      ( v2_pre_topc(sK1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_36,negated_conjecture,
% 3.31/0.99      ( ~ v2_struct_0(sK1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_37,negated_conjecture,
% 3.31/0.99      ( l1_pre_topc(sK0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_42,plain,
% 3.31/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_38,negated_conjecture,
% 3.31/0.99      ( v2_pre_topc(sK0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_39,negated_conjecture,
% 3.31/0.99      ( ~ v2_struct_0(sK0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(contradiction,plain,
% 3.31/0.99      ( $false ),
% 3.31/0.99      inference(minisat,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_10427,c_6510,c_5760,c_4849,c_4201,c_3445,c_3443,
% 3.31/0.99                 c_3359,c_3325,c_3189,c_2992,c_2968,c_2910,c_2824,c_2807,
% 3.31/0.99                 c_2626,c_2542,c_2265,c_2216,c_2174,c_2173,c_2162,c_2161,
% 3.31/0.99                 c_2160,c_2159,c_2114,c_1903,c_1822,c_1815,c_1000,c_986,
% 3.31/0.99                 c_21,c_25,c_26,c_27,c_30,c_31,c_46,c_33,c_34,c_35,c_36,
% 3.31/0.99                 c_42,c_37,c_38,c_39]) ).
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  ------                               Statistics
% 3.31/0.99  
% 3.31/0.99  ------ Selected
% 3.31/0.99  
% 3.31/0.99  total_time:                             0.305
% 3.31/0.99  
%------------------------------------------------------------------------------
