%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:39 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  231 (1163 expanded)
%              Number of clauses        :  140 ( 250 expanded)
%              Number of leaves         :   23 ( 518 expanded)
%              Depth                    :   27
%              Number of atoms          : 1422 (17094 expanded)
%              Number of equality atoms :  364 (2532 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f55,f54,f53,f52,f51,f50,f49])).

fof(f83,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
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
             => ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f42])).

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
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_887,plain,
    ( v3_pre_topc(k2_struct_0(X0_54),X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_22943,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_903,plain,
    ( ~ v3_pre_topc(X0_55,X0_54)
    | v3_pre_topc(X1_55,X0_54)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_2298,plain,
    ( v3_pre_topc(X0_55,X0_54)
    | ~ v3_pre_topc(k2_struct_0(X1_54),X0_54)
    | X0_55 != k2_struct_0(X1_54) ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_3333,plain,
    ( v3_pre_topc(u1_struct_0(X0_54),X1_54)
    | ~ v3_pre_topc(k2_struct_0(X0_54),X1_54)
    | u1_struct_0(X0_54) != k2_struct_0(X0_54) ),
    inference(instantiation,[status(thm)],[c_2298])).

cnf(c_13446,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2)
    | ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3333])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_886,plain,
    ( ~ v3_pre_topc(X0_55,X0_54)
    | v3_pre_topc(X0_55,X1_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3338,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0_54),X0_54)
    | v3_pre_topc(u1_struct_0(X0_54),X1_54)
    | ~ m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X0_54)))
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_8196,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3338])).

cnf(c_11,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_884,plain,
    ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5050,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_869,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1467,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_880,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1458,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_3354,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_1458])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_873,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3373,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3354,c_873])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3395,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_38,c_39,c_40,c_44])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_882,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(X0_54,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != k1_tsep_1(X1_54,X0_54,X2_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1456,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != k1_tsep_1(X1_54,X2_54,X0_54)
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_4289,plain,
    ( k1_tsep_1(X0_54,X1_54,sK2) != sK3
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X1_54,sK2) = iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_1456])).

cnf(c_4529,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(X1_54,sK2) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | k1_tsep_1(X0_54,X1_54,sK2) != sK3
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4289,c_44])).

cnf(c_4530,plain,
    ( k1_tsep_1(X0_54,X1_54,sK2) != sK3
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X1_54,sK2) = iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4529])).

cnf(c_4543,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_4530])).

cnf(c_45,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1877,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_1908,plain,
    ( ~ m1_pre_topc(X0_54,sK0)
    | m1_pre_topc(sK2,X0_54)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != k1_tsep_1(sK0,sK2,X0_54) ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_2212,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_2213,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2212])).

cnf(c_4983,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4543,c_37,c_38,c_36,c_39,c_35,c_40,c_31,c_44,c_30,c_45,c_1877,c_2213])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_885,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1453,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_2961,plain,
    ( m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(sK3,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_1453])).

cnf(c_4993,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4983,c_2961])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_375,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_861,plain,
    ( ~ l1_pre_topc(X0_54)
    | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_3760,plain,
    ( ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_883,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1455,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54)) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_883])).

cnf(c_3587,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_1455])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_877,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1461,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_21,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_876,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1515,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1461,c_876])).

cnf(c_9,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_201,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_11])).

cnf(c_202,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_458,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_459,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_463,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_27])).

cnf(c_464,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_463])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_507,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_464,c_16])).

cnf(c_530,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X5),X6)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_202,c_507])).

cnf(c_531,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X0),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_575,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X0),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_531,c_0,c_3])).

cnf(c_860,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
    | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
    | ~ v3_pre_topc(u1_struct_0(X0_54),X3_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_575])).

cnf(c_1476,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(X1_54) != u1_struct_0(sK3)
    | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X2_54),X1_54) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X1_54,X3_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_2765,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK3)
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1476])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3075,plain,
    ( v2_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2765,c_41,c_42,c_43])).

cnf(c_3076,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK3)
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3075])).

cnf(c_3093,plain,
    ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3076])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3135,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3093,c_46,c_50])).

cnf(c_3136,plain,
    ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3135])).

cnf(c_3152,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_3136])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_54,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_875,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1462,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_1500,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1462,c_876])).

cnf(c_3170,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3152,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1500])).

cnf(c_3171,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3170])).

cnf(c_3172,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3171])).

cnf(c_2907,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_889,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1449,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_2774,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_1449])).

cnf(c_2784,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2774])).

cnf(c_871,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1465,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_2773,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_1449])).

cnf(c_2783,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2773])).

cnf(c_2209,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k1_tsep_1(sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_1903,plain,
    ( ~ m1_pre_topc(X0_54,sK0)
    | m1_pre_topc(sK3,X0_54)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != k1_tsep_1(sK0,sK3,X0_54) ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_2200,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_881,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) = k1_tsep_1(X1_54,X0_54,X2_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1898,plain,
    ( ~ m1_pre_topc(X0_54,sK0)
    | ~ m1_pre_topc(sK2,X0_54)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(sK0,sK2,X0_54) ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_2185,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_2186,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK2,sK3)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2185])).

cnf(c_1893,plain,
    ( ~ m1_pre_topc(X0_54,sK0)
    | ~ m1_pre_topc(sK3,X0_54)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(sK0,sK3,X0_54) ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_2172,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_2173,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_890,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1448,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_1927,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_1448])).

cnf(c_1928,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1927])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22943,c_13446,c_8196,c_5050,c_4993,c_3760,c_3587,c_3172,c_2907,c_2784,c_2774,c_2783,c_2212,c_2209,c_2200,c_2186,c_2173,c_1928,c_1877,c_47,c_28,c_46,c_29,c_45,c_30,c_44,c_31,c_40,c_35,c_39,c_36,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.41/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/1.50  
% 7.41/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.41/1.50  
% 7.41/1.50  ------  iProver source info
% 7.41/1.50  
% 7.41/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.41/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.41/1.50  git: non_committed_changes: false
% 7.41/1.50  git: last_make_outside_of_git: false
% 7.41/1.50  
% 7.41/1.50  ------ 
% 7.41/1.50  
% 7.41/1.50  ------ Input Options
% 7.41/1.50  
% 7.41/1.50  --out_options                           all
% 7.41/1.50  --tptp_safe_out                         true
% 7.41/1.50  --problem_path                          ""
% 7.41/1.50  --include_path                          ""
% 7.41/1.50  --clausifier                            res/vclausify_rel
% 7.41/1.50  --clausifier_options                    --mode clausify
% 7.41/1.50  --stdin                                 false
% 7.41/1.50  --stats_out                             all
% 7.41/1.50  
% 7.41/1.50  ------ General Options
% 7.41/1.50  
% 7.41/1.50  --fof                                   false
% 7.41/1.50  --time_out_real                         305.
% 7.41/1.50  --time_out_virtual                      -1.
% 7.41/1.50  --symbol_type_check                     false
% 7.41/1.50  --clausify_out                          false
% 7.41/1.50  --sig_cnt_out                           false
% 7.41/1.50  --trig_cnt_out                          false
% 7.41/1.50  --trig_cnt_out_tolerance                1.
% 7.41/1.50  --trig_cnt_out_sk_spl                   false
% 7.41/1.50  --abstr_cl_out                          false
% 7.41/1.50  
% 7.41/1.50  ------ Global Options
% 7.41/1.50  
% 7.41/1.50  --schedule                              default
% 7.41/1.50  --add_important_lit                     false
% 7.41/1.50  --prop_solver_per_cl                    1000
% 7.41/1.50  --min_unsat_core                        false
% 7.41/1.50  --soft_assumptions                      false
% 7.41/1.50  --soft_lemma_size                       3
% 7.41/1.50  --prop_impl_unit_size                   0
% 7.41/1.50  --prop_impl_unit                        []
% 7.41/1.50  --share_sel_clauses                     true
% 7.41/1.50  --reset_solvers                         false
% 7.41/1.50  --bc_imp_inh                            [conj_cone]
% 7.41/1.50  --conj_cone_tolerance                   3.
% 7.41/1.50  --extra_neg_conj                        none
% 7.41/1.50  --large_theory_mode                     true
% 7.41/1.50  --prolific_symb_bound                   200
% 7.41/1.50  --lt_threshold                          2000
% 7.41/1.50  --clause_weak_htbl                      true
% 7.41/1.50  --gc_record_bc_elim                     false
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing Options
% 7.41/1.50  
% 7.41/1.50  --preprocessing_flag                    true
% 7.41/1.50  --time_out_prep_mult                    0.1
% 7.41/1.50  --splitting_mode                        input
% 7.41/1.50  --splitting_grd                         true
% 7.41/1.50  --splitting_cvd                         false
% 7.41/1.50  --splitting_cvd_svl                     false
% 7.41/1.50  --splitting_nvd                         32
% 7.41/1.50  --sub_typing                            true
% 7.41/1.50  --prep_gs_sim                           true
% 7.41/1.50  --prep_unflatten                        true
% 7.41/1.50  --prep_res_sim                          true
% 7.41/1.50  --prep_upred                            true
% 7.41/1.50  --prep_sem_filter                       exhaustive
% 7.41/1.50  --prep_sem_filter_out                   false
% 7.41/1.50  --pred_elim                             true
% 7.41/1.50  --res_sim_input                         true
% 7.41/1.50  --eq_ax_congr_red                       true
% 7.41/1.50  --pure_diseq_elim                       true
% 7.41/1.50  --brand_transform                       false
% 7.41/1.50  --non_eq_to_eq                          false
% 7.41/1.50  --prep_def_merge                        true
% 7.41/1.50  --prep_def_merge_prop_impl              false
% 7.41/1.50  --prep_def_merge_mbd                    true
% 7.41/1.50  --prep_def_merge_tr_red                 false
% 7.41/1.50  --prep_def_merge_tr_cl                  false
% 7.41/1.50  --smt_preprocessing                     true
% 7.41/1.50  --smt_ac_axioms                         fast
% 7.41/1.50  --preprocessed_out                      false
% 7.41/1.50  --preprocessed_stats                    false
% 7.41/1.50  
% 7.41/1.50  ------ Abstraction refinement Options
% 7.41/1.50  
% 7.41/1.50  --abstr_ref                             []
% 7.41/1.50  --abstr_ref_prep                        false
% 7.41/1.50  --abstr_ref_until_sat                   false
% 7.41/1.50  --abstr_ref_sig_restrict                funpre
% 7.41/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.50  --abstr_ref_under                       []
% 7.41/1.50  
% 7.41/1.50  ------ SAT Options
% 7.41/1.50  
% 7.41/1.50  --sat_mode                              false
% 7.41/1.50  --sat_fm_restart_options                ""
% 7.41/1.50  --sat_gr_def                            false
% 7.41/1.50  --sat_epr_types                         true
% 7.41/1.50  --sat_non_cyclic_types                  false
% 7.41/1.50  --sat_finite_models                     false
% 7.41/1.50  --sat_fm_lemmas                         false
% 7.41/1.50  --sat_fm_prep                           false
% 7.41/1.50  --sat_fm_uc_incr                        true
% 7.41/1.50  --sat_out_model                         small
% 7.41/1.50  --sat_out_clauses                       false
% 7.41/1.50  
% 7.41/1.50  ------ QBF Options
% 7.41/1.50  
% 7.41/1.50  --qbf_mode                              false
% 7.41/1.50  --qbf_elim_univ                         false
% 7.41/1.50  --qbf_dom_inst                          none
% 7.41/1.50  --qbf_dom_pre_inst                      false
% 7.41/1.50  --qbf_sk_in                             false
% 7.41/1.50  --qbf_pred_elim                         true
% 7.41/1.50  --qbf_split                             512
% 7.41/1.50  
% 7.41/1.50  ------ BMC1 Options
% 7.41/1.50  
% 7.41/1.50  --bmc1_incremental                      false
% 7.41/1.50  --bmc1_axioms                           reachable_all
% 7.41/1.50  --bmc1_min_bound                        0
% 7.41/1.50  --bmc1_max_bound                        -1
% 7.41/1.50  --bmc1_max_bound_default                -1
% 7.41/1.50  --bmc1_symbol_reachability              true
% 7.41/1.50  --bmc1_property_lemmas                  false
% 7.41/1.50  --bmc1_k_induction                      false
% 7.41/1.50  --bmc1_non_equiv_states                 false
% 7.41/1.50  --bmc1_deadlock                         false
% 7.41/1.50  --bmc1_ucm                              false
% 7.41/1.50  --bmc1_add_unsat_core                   none
% 7.41/1.50  --bmc1_unsat_core_children              false
% 7.41/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.50  --bmc1_out_stat                         full
% 7.41/1.50  --bmc1_ground_init                      false
% 7.41/1.50  --bmc1_pre_inst_next_state              false
% 7.41/1.50  --bmc1_pre_inst_state                   false
% 7.41/1.50  --bmc1_pre_inst_reach_state             false
% 7.41/1.50  --bmc1_out_unsat_core                   false
% 7.41/1.50  --bmc1_aig_witness_out                  false
% 7.41/1.50  --bmc1_verbose                          false
% 7.41/1.50  --bmc1_dump_clauses_tptp                false
% 7.41/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.50  --bmc1_dump_file                        -
% 7.41/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.50  --bmc1_ucm_extend_mode                  1
% 7.41/1.50  --bmc1_ucm_init_mode                    2
% 7.41/1.50  --bmc1_ucm_cone_mode                    none
% 7.41/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.50  --bmc1_ucm_relax_model                  4
% 7.41/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.50  --bmc1_ucm_layered_model                none
% 7.41/1.50  --bmc1_ucm_max_lemma_size               10
% 7.41/1.50  
% 7.41/1.50  ------ AIG Options
% 7.41/1.50  
% 7.41/1.50  --aig_mode                              false
% 7.41/1.50  
% 7.41/1.50  ------ Instantiation Options
% 7.41/1.50  
% 7.41/1.50  --instantiation_flag                    true
% 7.41/1.50  --inst_sos_flag                         false
% 7.41/1.50  --inst_sos_phase                        true
% 7.41/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel_side                     num_symb
% 7.41/1.50  --inst_solver_per_active                1400
% 7.41/1.50  --inst_solver_calls_frac                1.
% 7.41/1.50  --inst_passive_queue_type               priority_queues
% 7.41/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.50  --inst_passive_queues_freq              [25;2]
% 7.41/1.50  --inst_dismatching                      true
% 7.41/1.50  --inst_eager_unprocessed_to_passive     true
% 7.41/1.50  --inst_prop_sim_given                   true
% 7.41/1.50  --inst_prop_sim_new                     false
% 7.41/1.50  --inst_subs_new                         false
% 7.41/1.50  --inst_eq_res_simp                      false
% 7.41/1.50  --inst_subs_given                       false
% 7.41/1.50  --inst_orphan_elimination               true
% 7.41/1.50  --inst_learning_loop_flag               true
% 7.41/1.50  --inst_learning_start                   3000
% 7.41/1.50  --inst_learning_factor                  2
% 7.41/1.50  --inst_start_prop_sim_after_learn       3
% 7.41/1.50  --inst_sel_renew                        solver
% 7.41/1.50  --inst_lit_activity_flag                true
% 7.41/1.50  --inst_restr_to_given                   false
% 7.41/1.50  --inst_activity_threshold               500
% 7.41/1.50  --inst_out_proof                        true
% 7.41/1.50  
% 7.41/1.50  ------ Resolution Options
% 7.41/1.50  
% 7.41/1.50  --resolution_flag                       true
% 7.41/1.50  --res_lit_sel                           adaptive
% 7.41/1.50  --res_lit_sel_side                      none
% 7.41/1.50  --res_ordering                          kbo
% 7.41/1.50  --res_to_prop_solver                    active
% 7.41/1.50  --res_prop_simpl_new                    false
% 7.41/1.50  --res_prop_simpl_given                  true
% 7.41/1.50  --res_passive_queue_type                priority_queues
% 7.41/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.50  --res_passive_queues_freq               [15;5]
% 7.41/1.50  --res_forward_subs                      full
% 7.41/1.50  --res_backward_subs                     full
% 7.41/1.50  --res_forward_subs_resolution           true
% 7.41/1.50  --res_backward_subs_resolution          true
% 7.41/1.50  --res_orphan_elimination                true
% 7.41/1.50  --res_time_limit                        2.
% 7.41/1.50  --res_out_proof                         true
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Options
% 7.41/1.50  
% 7.41/1.50  --superposition_flag                    true
% 7.41/1.50  --sup_passive_queue_type                priority_queues
% 7.41/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.50  --demod_completeness_check              fast
% 7.41/1.50  --demod_use_ground                      true
% 7.41/1.50  --sup_to_prop_solver                    passive
% 7.41/1.50  --sup_prop_simpl_new                    true
% 7.41/1.50  --sup_prop_simpl_given                  true
% 7.41/1.50  --sup_fun_splitting                     false
% 7.41/1.50  --sup_smt_interval                      50000
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Simplification Setup
% 7.41/1.50  
% 7.41/1.50  --sup_indices_passive                   []
% 7.41/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_full_bw                           [BwDemod]
% 7.41/1.50  --sup_immed_triv                        [TrivRules]
% 7.41/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_immed_bw_main                     []
% 7.41/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  
% 7.41/1.50  ------ Combination Options
% 7.41/1.50  
% 7.41/1.50  --comb_res_mult                         3
% 7.41/1.50  --comb_sup_mult                         2
% 7.41/1.50  --comb_inst_mult                        10
% 7.41/1.50  
% 7.41/1.50  ------ Debug Options
% 7.41/1.50  
% 7.41/1.50  --dbg_backtrace                         false
% 7.41/1.50  --dbg_dump_prop_clauses                 false
% 7.41/1.50  --dbg_dump_prop_clauses_file            -
% 7.41/1.50  --dbg_out_stat                          false
% 7.41/1.50  ------ Parsing...
% 7.41/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.41/1.50  ------ Proving...
% 7.41/1.50  ------ Problem Properties 
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  clauses                                 32
% 7.41/1.50  conjectures                             17
% 7.41/1.50  EPR                                     15
% 7.41/1.50  Horn                                    26
% 7.41/1.50  unary                                   17
% 7.41/1.50  binary                                  1
% 7.41/1.50  lits                                    118
% 7.41/1.50  lits eq                                 10
% 7.41/1.50  fd_pure                                 0
% 7.41/1.50  fd_pseudo                               0
% 7.41/1.50  fd_cond                                 0
% 7.41/1.50  fd_pseudo_cond                          0
% 7.41/1.50  AC symbols                              0
% 7.41/1.50  
% 7.41/1.50  ------ Schedule dynamic 5 is on 
% 7.41/1.50  
% 7.41/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  ------ 
% 7.41/1.50  Current options:
% 7.41/1.50  ------ 
% 7.41/1.50  
% 7.41/1.50  ------ Input Options
% 7.41/1.50  
% 7.41/1.50  --out_options                           all
% 7.41/1.50  --tptp_safe_out                         true
% 7.41/1.50  --problem_path                          ""
% 7.41/1.50  --include_path                          ""
% 7.41/1.50  --clausifier                            res/vclausify_rel
% 7.41/1.50  --clausifier_options                    --mode clausify
% 7.41/1.50  --stdin                                 false
% 7.41/1.50  --stats_out                             all
% 7.41/1.50  
% 7.41/1.50  ------ General Options
% 7.41/1.50  
% 7.41/1.50  --fof                                   false
% 7.41/1.50  --time_out_real                         305.
% 7.41/1.50  --time_out_virtual                      -1.
% 7.41/1.50  --symbol_type_check                     false
% 7.41/1.50  --clausify_out                          false
% 7.41/1.50  --sig_cnt_out                           false
% 7.41/1.50  --trig_cnt_out                          false
% 7.41/1.50  --trig_cnt_out_tolerance                1.
% 7.41/1.50  --trig_cnt_out_sk_spl                   false
% 7.41/1.50  --abstr_cl_out                          false
% 7.41/1.50  
% 7.41/1.50  ------ Global Options
% 7.41/1.50  
% 7.41/1.50  --schedule                              default
% 7.41/1.50  --add_important_lit                     false
% 7.41/1.50  --prop_solver_per_cl                    1000
% 7.41/1.50  --min_unsat_core                        false
% 7.41/1.50  --soft_assumptions                      false
% 7.41/1.50  --soft_lemma_size                       3
% 7.41/1.50  --prop_impl_unit_size                   0
% 7.41/1.50  --prop_impl_unit                        []
% 7.41/1.50  --share_sel_clauses                     true
% 7.41/1.50  --reset_solvers                         false
% 7.41/1.50  --bc_imp_inh                            [conj_cone]
% 7.41/1.50  --conj_cone_tolerance                   3.
% 7.41/1.50  --extra_neg_conj                        none
% 7.41/1.50  --large_theory_mode                     true
% 7.41/1.50  --prolific_symb_bound                   200
% 7.41/1.50  --lt_threshold                          2000
% 7.41/1.50  --clause_weak_htbl                      true
% 7.41/1.50  --gc_record_bc_elim                     false
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing Options
% 7.41/1.50  
% 7.41/1.50  --preprocessing_flag                    true
% 7.41/1.50  --time_out_prep_mult                    0.1
% 7.41/1.50  --splitting_mode                        input
% 7.41/1.50  --splitting_grd                         true
% 7.41/1.50  --splitting_cvd                         false
% 7.41/1.50  --splitting_cvd_svl                     false
% 7.41/1.50  --splitting_nvd                         32
% 7.41/1.50  --sub_typing                            true
% 7.41/1.50  --prep_gs_sim                           true
% 7.41/1.50  --prep_unflatten                        true
% 7.41/1.50  --prep_res_sim                          true
% 7.41/1.50  --prep_upred                            true
% 7.41/1.50  --prep_sem_filter                       exhaustive
% 7.41/1.50  --prep_sem_filter_out                   false
% 7.41/1.50  --pred_elim                             true
% 7.41/1.50  --res_sim_input                         true
% 7.41/1.50  --eq_ax_congr_red                       true
% 7.41/1.50  --pure_diseq_elim                       true
% 7.41/1.50  --brand_transform                       false
% 7.41/1.50  --non_eq_to_eq                          false
% 7.41/1.50  --prep_def_merge                        true
% 7.41/1.50  --prep_def_merge_prop_impl              false
% 7.41/1.50  --prep_def_merge_mbd                    true
% 7.41/1.50  --prep_def_merge_tr_red                 false
% 7.41/1.50  --prep_def_merge_tr_cl                  false
% 7.41/1.50  --smt_preprocessing                     true
% 7.41/1.50  --smt_ac_axioms                         fast
% 7.41/1.50  --preprocessed_out                      false
% 7.41/1.50  --preprocessed_stats                    false
% 7.41/1.50  
% 7.41/1.50  ------ Abstraction refinement Options
% 7.41/1.50  
% 7.41/1.50  --abstr_ref                             []
% 7.41/1.50  --abstr_ref_prep                        false
% 7.41/1.50  --abstr_ref_until_sat                   false
% 7.41/1.50  --abstr_ref_sig_restrict                funpre
% 7.41/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.50  --abstr_ref_under                       []
% 7.41/1.50  
% 7.41/1.50  ------ SAT Options
% 7.41/1.50  
% 7.41/1.50  --sat_mode                              false
% 7.41/1.50  --sat_fm_restart_options                ""
% 7.41/1.50  --sat_gr_def                            false
% 7.41/1.50  --sat_epr_types                         true
% 7.41/1.50  --sat_non_cyclic_types                  false
% 7.41/1.50  --sat_finite_models                     false
% 7.41/1.50  --sat_fm_lemmas                         false
% 7.41/1.50  --sat_fm_prep                           false
% 7.41/1.50  --sat_fm_uc_incr                        true
% 7.41/1.50  --sat_out_model                         small
% 7.41/1.50  --sat_out_clauses                       false
% 7.41/1.50  
% 7.41/1.50  ------ QBF Options
% 7.41/1.50  
% 7.41/1.50  --qbf_mode                              false
% 7.41/1.50  --qbf_elim_univ                         false
% 7.41/1.50  --qbf_dom_inst                          none
% 7.41/1.50  --qbf_dom_pre_inst                      false
% 7.41/1.50  --qbf_sk_in                             false
% 7.41/1.50  --qbf_pred_elim                         true
% 7.41/1.50  --qbf_split                             512
% 7.41/1.50  
% 7.41/1.50  ------ BMC1 Options
% 7.41/1.50  
% 7.41/1.50  --bmc1_incremental                      false
% 7.41/1.50  --bmc1_axioms                           reachable_all
% 7.41/1.50  --bmc1_min_bound                        0
% 7.41/1.50  --bmc1_max_bound                        -1
% 7.41/1.50  --bmc1_max_bound_default                -1
% 7.41/1.50  --bmc1_symbol_reachability              true
% 7.41/1.50  --bmc1_property_lemmas                  false
% 7.41/1.50  --bmc1_k_induction                      false
% 7.41/1.50  --bmc1_non_equiv_states                 false
% 7.41/1.50  --bmc1_deadlock                         false
% 7.41/1.50  --bmc1_ucm                              false
% 7.41/1.50  --bmc1_add_unsat_core                   none
% 7.41/1.50  --bmc1_unsat_core_children              false
% 7.41/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.50  --bmc1_out_stat                         full
% 7.41/1.50  --bmc1_ground_init                      false
% 7.41/1.50  --bmc1_pre_inst_next_state              false
% 7.41/1.50  --bmc1_pre_inst_state                   false
% 7.41/1.50  --bmc1_pre_inst_reach_state             false
% 7.41/1.50  --bmc1_out_unsat_core                   false
% 7.41/1.50  --bmc1_aig_witness_out                  false
% 7.41/1.50  --bmc1_verbose                          false
% 7.41/1.50  --bmc1_dump_clauses_tptp                false
% 7.41/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.50  --bmc1_dump_file                        -
% 7.41/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.50  --bmc1_ucm_extend_mode                  1
% 7.41/1.50  --bmc1_ucm_init_mode                    2
% 7.41/1.50  --bmc1_ucm_cone_mode                    none
% 7.41/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.50  --bmc1_ucm_relax_model                  4
% 7.41/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.50  --bmc1_ucm_layered_model                none
% 7.41/1.50  --bmc1_ucm_max_lemma_size               10
% 7.41/1.50  
% 7.41/1.50  ------ AIG Options
% 7.41/1.50  
% 7.41/1.50  --aig_mode                              false
% 7.41/1.50  
% 7.41/1.50  ------ Instantiation Options
% 7.41/1.50  
% 7.41/1.50  --instantiation_flag                    true
% 7.41/1.50  --inst_sos_flag                         false
% 7.41/1.50  --inst_sos_phase                        true
% 7.41/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel_side                     none
% 7.41/1.50  --inst_solver_per_active                1400
% 7.41/1.50  --inst_solver_calls_frac                1.
% 7.41/1.50  --inst_passive_queue_type               priority_queues
% 7.41/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.50  --inst_passive_queues_freq              [25;2]
% 7.41/1.50  --inst_dismatching                      true
% 7.41/1.50  --inst_eager_unprocessed_to_passive     true
% 7.41/1.50  --inst_prop_sim_given                   true
% 7.41/1.50  --inst_prop_sim_new                     false
% 7.41/1.50  --inst_subs_new                         false
% 7.41/1.50  --inst_eq_res_simp                      false
% 7.41/1.50  --inst_subs_given                       false
% 7.41/1.50  --inst_orphan_elimination               true
% 7.41/1.50  --inst_learning_loop_flag               true
% 7.41/1.50  --inst_learning_start                   3000
% 7.41/1.50  --inst_learning_factor                  2
% 7.41/1.50  --inst_start_prop_sim_after_learn       3
% 7.41/1.50  --inst_sel_renew                        solver
% 7.41/1.50  --inst_lit_activity_flag                true
% 7.41/1.50  --inst_restr_to_given                   false
% 7.41/1.50  --inst_activity_threshold               500
% 7.41/1.50  --inst_out_proof                        true
% 7.41/1.50  
% 7.41/1.50  ------ Resolution Options
% 7.41/1.50  
% 7.41/1.50  --resolution_flag                       false
% 7.41/1.50  --res_lit_sel                           adaptive
% 7.41/1.50  --res_lit_sel_side                      none
% 7.41/1.50  --res_ordering                          kbo
% 7.41/1.50  --res_to_prop_solver                    active
% 7.41/1.50  --res_prop_simpl_new                    false
% 7.41/1.50  --res_prop_simpl_given                  true
% 7.41/1.50  --res_passive_queue_type                priority_queues
% 7.41/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.50  --res_passive_queues_freq               [15;5]
% 7.41/1.50  --res_forward_subs                      full
% 7.41/1.50  --res_backward_subs                     full
% 7.41/1.50  --res_forward_subs_resolution           true
% 7.41/1.50  --res_backward_subs_resolution          true
% 7.41/1.50  --res_orphan_elimination                true
% 7.41/1.50  --res_time_limit                        2.
% 7.41/1.50  --res_out_proof                         true
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Options
% 7.41/1.50  
% 7.41/1.50  --superposition_flag                    true
% 7.41/1.50  --sup_passive_queue_type                priority_queues
% 7.41/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.50  --demod_completeness_check              fast
% 7.41/1.50  --demod_use_ground                      true
% 7.41/1.50  --sup_to_prop_solver                    passive
% 7.41/1.50  --sup_prop_simpl_new                    true
% 7.41/1.50  --sup_prop_simpl_given                  true
% 7.41/1.50  --sup_fun_splitting                     false
% 7.41/1.50  --sup_smt_interval                      50000
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Simplification Setup
% 7.41/1.50  
% 7.41/1.50  --sup_indices_passive                   []
% 7.41/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_full_bw                           [BwDemod]
% 7.41/1.50  --sup_immed_triv                        [TrivRules]
% 7.41/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_immed_bw_main                     []
% 7.41/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  
% 7.41/1.50  ------ Combination Options
% 7.41/1.50  
% 7.41/1.50  --comb_res_mult                         3
% 7.41/1.50  --comb_sup_mult                         2
% 7.41/1.50  --comb_inst_mult                        10
% 7.41/1.50  
% 7.41/1.50  ------ Debug Options
% 7.41/1.50  
% 7.41/1.50  --dbg_backtrace                         false
% 7.41/1.50  --dbg_dump_prop_clauses                 false
% 7.41/1.50  --dbg_dump_prop_clauses_file            -
% 7.41/1.50  --dbg_out_stat                          false
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  ------ Proving...
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  % SZS status Theorem for theBenchmark.p
% 7.41/1.50  
% 7.41/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.41/1.50  
% 7.41/1.50  fof(f6,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f25,plain,(
% 7.41/1.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f6])).
% 7.41/1.50  
% 7.41/1.50  fof(f26,plain,(
% 7.41/1.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.41/1.50    inference(flattening,[],[f25])).
% 7.41/1.50  
% 7.41/1.50  fof(f62,plain,(
% 7.41/1.50    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f26])).
% 7.41/1.50  
% 7.41/1.50  fof(f7,axiom,(
% 7.41/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f27,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f7])).
% 7.41/1.50  
% 7.41/1.50  fof(f28,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.41/1.50    inference(flattening,[],[f27])).
% 7.41/1.50  
% 7.41/1.50  fof(f63,plain,(
% 7.41/1.50    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f28])).
% 7.41/1.50  
% 7.41/1.50  fof(f95,plain,(
% 7.41/1.50    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.41/1.50    inference(equality_resolution,[],[f63])).
% 7.41/1.50  
% 7.41/1.50  fof(f10,axiom,(
% 7.41/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f32,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f10])).
% 7.41/1.50  
% 7.41/1.50  fof(f68,plain,(
% 7.41/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f32])).
% 7.41/1.50  
% 7.41/1.50  fof(f16,conjecture,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f17,negated_conjecture,(
% 7.41/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.41/1.50    inference(negated_conjecture,[],[f16])).
% 7.41/1.50  
% 7.41/1.50  fof(f43,plain,(
% 7.41/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f17])).
% 7.41/1.50  
% 7.41/1.50  fof(f44,plain,(
% 7.41/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f43])).
% 7.41/1.50  
% 7.41/1.50  fof(f55,plain,(
% 7.41/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f54,plain,(
% 7.41/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f53,plain,(
% 7.41/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f52,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f51,plain,(
% 7.41/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f50,plain,(
% 7.41/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f49,plain,(
% 7.41/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f56,plain,(
% 7.41/1.50    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.41/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f55,f54,f53,f52,f51,f50,f49])).
% 7.41/1.50  
% 7.41/1.50  fof(f83,plain,(
% 7.41/1.50    m1_pre_topc(sK2,sK0)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f13,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f37,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f13])).
% 7.41/1.50  
% 7.41/1.50  fof(f38,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f37])).
% 7.41/1.50  
% 7.41/1.50  fof(f72,plain,(
% 7.41/1.50    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f38])).
% 7.41/1.50  
% 7.41/1.50  fof(f89,plain,(
% 7.41/1.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f76,plain,(
% 7.41/1.50    ~v2_struct_0(sK0)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f77,plain,(
% 7.41/1.50    v2_pre_topc(sK0)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f78,plain,(
% 7.41/1.50    l1_pre_topc(sK0)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f82,plain,(
% 7.41/1.50    ~v2_struct_0(sK2)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f12,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f35,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f12])).
% 7.41/1.50  
% 7.41/1.50  fof(f36,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f35])).
% 7.41/1.50  
% 7.41/1.50  fof(f47,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(nnf_transformation,[],[f36])).
% 7.41/1.50  
% 7.41/1.50  fof(f71,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f47])).
% 7.41/1.50  
% 7.41/1.50  fof(f8,axiom,(
% 7.41/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f18,plain,(
% 7.41/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 7.41/1.50    inference(pure_predicate_removal,[],[f8])).
% 7.41/1.50  
% 7.41/1.50  fof(f29,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f18])).
% 7.41/1.50  
% 7.41/1.50  fof(f64,plain,(
% 7.41/1.50    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f29])).
% 7.41/1.50  
% 7.41/1.50  fof(f3,axiom,(
% 7.41/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f22,plain,(
% 7.41/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f3])).
% 7.41/1.50  
% 7.41/1.50  fof(f59,plain,(
% 7.41/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f22])).
% 7.41/1.50  
% 7.41/1.50  fof(f2,axiom,(
% 7.41/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f21,plain,(
% 7.41/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f2])).
% 7.41/1.50  
% 7.41/1.50  fof(f58,plain,(
% 7.41/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f21])).
% 7.41/1.50  
% 7.41/1.50  fof(f11,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f33,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f11])).
% 7.41/1.50  
% 7.41/1.50  fof(f34,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f33])).
% 7.41/1.50  
% 7.41/1.50  fof(f69,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f34])).
% 7.41/1.50  
% 7.41/1.50  fof(f93,plain,(
% 7.41/1.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f92,plain,(
% 7.41/1.50    sK5 = sK6),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f9,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f30,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f9])).
% 7.41/1.50  
% 7.41/1.50  fof(f31,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.41/1.50    inference(flattening,[],[f30])).
% 7.41/1.50  
% 7.41/1.50  fof(f45,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.41/1.50    inference(nnf_transformation,[],[f31])).
% 7.41/1.50  
% 7.41/1.50  fof(f46,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.41/1.50    inference(flattening,[],[f45])).
% 7.41/1.50  
% 7.41/1.50  fof(f66,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f46])).
% 7.41/1.50  
% 7.41/1.50  fof(f97,plain,(
% 7.41/1.50    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.41/1.50    inference(equality_resolution,[],[f66])).
% 7.41/1.50  
% 7.41/1.50  fof(f15,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f41,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f15])).
% 7.41/1.50  
% 7.41/1.50  fof(f42,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f41])).
% 7.41/1.50  
% 7.41/1.50  fof(f48,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(nnf_transformation,[],[f42])).
% 7.41/1.50  
% 7.41/1.50  fof(f75,plain,(
% 7.41/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f48])).
% 7.41/1.50  
% 7.41/1.50  fof(f99,plain,(
% 7.41/1.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(equality_resolution,[],[f75])).
% 7.41/1.50  
% 7.41/1.50  fof(f87,plain,(
% 7.41/1.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f86,plain,(
% 7.41/1.50    v1_funct_1(sK4)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f14,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f39,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f14])).
% 7.41/1.50  
% 7.41/1.50  fof(f40,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.41/1.50    inference(flattening,[],[f39])).
% 7.41/1.50  
% 7.41/1.50  fof(f73,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f40])).
% 7.41/1.50  
% 7.41/1.50  fof(f1,axiom,(
% 7.41/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f19,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f1])).
% 7.41/1.50  
% 7.41/1.50  fof(f20,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.41/1.50    inference(flattening,[],[f19])).
% 7.41/1.50  
% 7.41/1.50  fof(f57,plain,(
% 7.41/1.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f20])).
% 7.41/1.50  
% 7.41/1.50  fof(f4,axiom,(
% 7.41/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.41/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f23,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f4])).
% 7.41/1.50  
% 7.41/1.50  fof(f60,plain,(
% 7.41/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f23])).
% 7.41/1.50  
% 7.41/1.50  fof(f79,plain,(
% 7.41/1.50    ~v2_struct_0(sK1)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f80,plain,(
% 7.41/1.50    v2_pre_topc(sK1)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f81,plain,(
% 7.41/1.50    l1_pre_topc(sK1)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f84,plain,(
% 7.41/1.50    ~v2_struct_0(sK3)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f88,plain,(
% 7.41/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f85,plain,(
% 7.41/1.50    m1_pre_topc(sK3,sK0)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f90,plain,(
% 7.41/1.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f94,plain,(
% 7.41/1.50    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f91,plain,(
% 7.41/1.50    m1_subset_1(sK6,u1_struct_0(sK2))),
% 7.41/1.50    inference(cnf_transformation,[],[f56])).
% 7.41/1.50  
% 7.41/1.50  fof(f70,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f47])).
% 7.41/1.50  
% 7.41/1.50  cnf(c_5,plain,
% 7.41/1.50      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.41/1.50      | ~ l1_pre_topc(X0)
% 7.41/1.50      | ~ v2_pre_topc(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_887,plain,
% 7.41/1.50      ( v3_pre_topc(k2_struct_0(X0_54),X0_54)
% 7.41/1.50      | ~ l1_pre_topc(X0_54)
% 7.41/1.50      | ~ v2_pre_topc(X0_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_22943,plain,
% 7.41/1.50      ( v3_pre_topc(k2_struct_0(sK2),sK2)
% 7.41/1.50      | ~ l1_pre_topc(sK2)
% 7.41/1.50      | ~ v2_pre_topc(sK2) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_887]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_903,plain,
% 7.41/1.50      ( ~ v3_pre_topc(X0_55,X0_54)
% 7.41/1.50      | v3_pre_topc(X1_55,X0_54)
% 7.41/1.50      | X1_55 != X0_55 ),
% 7.41/1.50      theory(equality) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2298,plain,
% 7.41/1.50      ( v3_pre_topc(X0_55,X0_54)
% 7.41/1.50      | ~ v3_pre_topc(k2_struct_0(X1_54),X0_54)
% 7.41/1.50      | X0_55 != k2_struct_0(X1_54) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_903]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3333,plain,
% 7.41/1.50      ( v3_pre_topc(u1_struct_0(X0_54),X1_54)
% 7.41/1.50      | ~ v3_pre_topc(k2_struct_0(X0_54),X1_54)
% 7.41/1.50      | u1_struct_0(X0_54) != k2_struct_0(X0_54) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_2298]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_13446,plain,
% 7.41/1.50      ( v3_pre_topc(u1_struct_0(sK2),sK2)
% 7.41/1.50      | ~ v3_pre_topc(k2_struct_0(sK2),sK2)
% 7.41/1.50      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_3333]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_6,plain,
% 7.41/1.50      ( ~ v3_pre_topc(X0,X1)
% 7.41/1.50      | v3_pre_topc(X0,X2)
% 7.41/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.41/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | ~ m1_pre_topc(X2,X1)
% 7.41/1.50      | ~ l1_pre_topc(X1) ),
% 7.41/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_886,plain,
% 7.41/1.50      ( ~ v3_pre_topc(X0_55,X0_54)
% 7.41/1.50      | v3_pre_topc(X0_55,X1_54)
% 7.41/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
% 7.41/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
% 7.41/1.50      | ~ m1_pre_topc(X1_54,X0_54)
% 7.41/1.50      | ~ l1_pre_topc(X0_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3338,plain,
% 7.41/1.50      ( ~ v3_pre_topc(u1_struct_0(X0_54),X0_54)
% 7.41/1.50      | v3_pre_topc(u1_struct_0(X0_54),X1_54)
% 7.41/1.50      | ~ m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
% 7.41/1.50      | ~ m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X0_54)))
% 7.41/1.50      | ~ m1_pre_topc(X1_54,X0_54)
% 7.41/1.50      | ~ l1_pre_topc(X0_54) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_886]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_8196,plain,
% 7.41/1.50      ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
% 7.41/1.50      | v3_pre_topc(u1_struct_0(sK2),sK3)
% 7.41/1.50      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.41/1.50      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ m1_pre_topc(sK3,sK2)
% 7.41/1.50      | ~ l1_pre_topc(sK2) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_3338]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_11,plain,
% 7.41/1.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | ~ m1_pre_topc(X0,X1)
% 7.41/1.50      | ~ l1_pre_topc(X1) ),
% 7.41/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_884,plain,
% 7.41/1.50      ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
% 7.41/1.50      | ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.50      | ~ l1_pre_topc(X1_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_5050,plain,
% 7.41/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ m1_pre_topc(sK2,sK3)
% 7.41/1.50      | ~ l1_pre_topc(sK3) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_884]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_30,negated_conjecture,
% 7.41/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_869,negated_conjecture,
% 7.41/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_30]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1467,plain,
% 7.41/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_15,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | v2_struct_0(X0)
% 7.41/1.50      | ~ l1_pre_topc(X1)
% 7.41/1.50      | ~ v2_pre_topc(X1)
% 7.41/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_880,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.50      | v2_struct_0(X1_54)
% 7.41/1.50      | v2_struct_0(X0_54)
% 7.41/1.50      | ~ l1_pre_topc(X1_54)
% 7.41/1.50      | ~ v2_pre_topc(X1_54)
% 7.41/1.50      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1458,plain,
% 7.41/1.50      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54)
% 7.41/1.50      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.41/1.50      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.50      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.50      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.50      | v2_pre_topc(X1_54) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_880]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3354,plain,
% 7.41/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 7.41/1.50      | v2_struct_0(sK0) = iProver_top
% 7.41/1.50      | v2_struct_0(sK2) = iProver_top
% 7.41/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1467,c_1458]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_24,negated_conjecture,
% 7.41/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.41/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_873,negated_conjecture,
% 7.41/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_24]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3373,plain,
% 7.41/1.50      ( k1_tsep_1(sK0,sK2,sK2) = sK3
% 7.41/1.50      | v2_struct_0(sK0) = iProver_top
% 7.41/1.50      | v2_struct_0(sK2) = iProver_top
% 7.41/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_3354,c_873]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_37,negated_conjecture,
% 7.41/1.50      ( ~ v2_struct_0(sK0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_38,plain,
% 7.41/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_36,negated_conjecture,
% 7.41/1.50      ( v2_pre_topc(sK0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_39,plain,
% 7.41/1.50      ( v2_pre_topc(sK0) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_35,negated_conjecture,
% 7.41/1.50      ( l1_pre_topc(sK0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_40,plain,
% 7.41/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_31,negated_conjecture,
% 7.41/1.50      ( ~ v2_struct_0(sK2) ),
% 7.41/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_44,plain,
% 7.41/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3395,plain,
% 7.41/1.50      ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_3373,c_38,c_39,c_40,c_44]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_13,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.41/1.50      | ~ m1_pre_topc(X2,X1)
% 7.41/1.50      | m1_pre_topc(X0,X2)
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | v2_struct_0(X0)
% 7.41/1.50      | v2_struct_0(X2)
% 7.41/1.50      | ~ l1_pre_topc(X1)
% 7.41/1.50      | ~ v2_pre_topc(X1)
% 7.41/1.50      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X1,X0,X2) ),
% 7.41/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_882,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.50      | ~ m1_pre_topc(X2_54,X1_54)
% 7.41/1.50      | m1_pre_topc(X0_54,X2_54)
% 7.41/1.50      | v2_struct_0(X1_54)
% 7.41/1.50      | v2_struct_0(X0_54)
% 7.41/1.50      | v2_struct_0(X2_54)
% 7.41/1.50      | ~ l1_pre_topc(X1_54)
% 7.41/1.50      | ~ v2_pre_topc(X1_54)
% 7.41/1.50      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != k1_tsep_1(X1_54,X0_54,X2_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1456,plain,
% 7.41/1.50      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != k1_tsep_1(X1_54,X2_54,X0_54)
% 7.41/1.50      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.41/1.50      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.41/1.50      | m1_pre_topc(X2_54,X0_54) = iProver_top
% 7.41/1.50      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.50      | v2_struct_0(X2_54) = iProver_top
% 7.41/1.50      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.50      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.50      | v2_pre_topc(X1_54) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_882]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_4289,plain,
% 7.41/1.50      ( k1_tsep_1(X0_54,X1_54,sK2) != sK3
% 7.41/1.50      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.41/1.50      | m1_pre_topc(X1_54,sK2) = iProver_top
% 7.41/1.50      | m1_pre_topc(sK2,X0_54) != iProver_top
% 7.41/1.50      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.50      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.50      | v2_struct_0(sK2) = iProver_top
% 7.41/1.50      | l1_pre_topc(X0_54) != iProver_top
% 7.41/1.50      | v2_pre_topc(X0_54) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_873,c_1456]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_4529,plain,
% 7.41/1.50      ( v2_struct_0(X0_54) = iProver_top
% 7.41/1.50      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.50      | m1_pre_topc(sK2,X0_54) != iProver_top
% 7.41/1.50      | m1_pre_topc(X1_54,sK2) = iProver_top
% 7.41/1.50      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.41/1.50      | k1_tsep_1(X0_54,X1_54,sK2) != sK3
% 7.41/1.50      | l1_pre_topc(X0_54) != iProver_top
% 7.41/1.50      | v2_pre_topc(X0_54) != iProver_top ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_4289,c_44]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_4530,plain,
% 7.41/1.50      ( k1_tsep_1(X0_54,X1_54,sK2) != sK3
% 7.41/1.50      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.41/1.50      | m1_pre_topc(X1_54,sK2) = iProver_top
% 7.41/1.50      | m1_pre_topc(sK2,X0_54) != iProver_top
% 7.41/1.50      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.50      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.50      | l1_pre_topc(X0_54) != iProver_top
% 7.41/1.50      | v2_pre_topc(X0_54) != iProver_top ),
% 7.41/1.50      inference(renaming,[status(thm)],[c_4529]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_4543,plain,
% 7.41/1.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.41/1.50      | m1_pre_topc(sK2,sK2) = iProver_top
% 7.41/1.50      | v2_struct_0(sK0) = iProver_top
% 7.41/1.50      | v2_struct_0(sK2) = iProver_top
% 7.41/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_3395,c_4530]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_45,plain,
% 7.41/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1877,plain,
% 7.41/1.50      ( ~ m1_pre_topc(sK2,sK0)
% 7.41/1.50      | v2_struct_0(sK0)
% 7.41/1.50      | v2_struct_0(sK2)
% 7.41/1.50      | ~ l1_pre_topc(sK0)
% 7.41/1.50      | ~ v2_pre_topc(sK0)
% 7.41/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_880]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1908,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0_54,sK0)
% 7.41/1.50      | m1_pre_topc(sK2,X0_54)
% 7.41/1.50      | ~ m1_pre_topc(sK2,sK0)
% 7.41/1.50      | v2_struct_0(X0_54)
% 7.41/1.50      | v2_struct_0(sK0)
% 7.41/1.50      | v2_struct_0(sK2)
% 7.41/1.50      | ~ l1_pre_topc(sK0)
% 7.41/1.50      | ~ v2_pre_topc(sK0)
% 7.41/1.50      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != k1_tsep_1(sK0,sK2,X0_54) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_882]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2212,plain,
% 7.41/1.50      ( ~ m1_pre_topc(sK2,sK0)
% 7.41/1.50      | m1_pre_topc(sK2,sK2)
% 7.41/1.50      | v2_struct_0(sK0)
% 7.41/1.50      | v2_struct_0(sK2)
% 7.41/1.50      | ~ l1_pre_topc(sK0)
% 7.41/1.50      | ~ v2_pre_topc(sK0)
% 7.41/1.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_1908]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2213,plain,
% 7.41/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2)
% 7.41/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.41/1.50      | m1_pre_topc(sK2,sK2) = iProver_top
% 7.41/1.50      | v2_struct_0(sK0) = iProver_top
% 7.41/1.50      | v2_struct_0(sK2) = iProver_top
% 7.41/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_2212]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_4983,plain,
% 7.41/1.50      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_4543,c_37,c_38,c_36,c_39,c_35,c_40,c_31,c_44,c_30,
% 7.41/1.50                 c_45,c_1877,c_2213]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_7,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.41/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.41/1.50      | ~ l1_pre_topc(X1) ),
% 7.41/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_885,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
% 7.41/1.50      | ~ l1_pre_topc(X1_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1453,plain,
% 7.41/1.50      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.41/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) = iProver_top
% 7.41/1.50      | l1_pre_topc(X1_54) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_885]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2961,plain,
% 7.41/1.50      ( m1_pre_topc(sK2,X0_54) != iProver_top
% 7.41/1.50      | m1_pre_topc(sK3,X0_54) = iProver_top
% 7.41/1.50      | l1_pre_topc(X0_54) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_873,c_1453]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_4993,plain,
% 7.41/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top
% 7.41/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_4983,c_2961]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2,plain,
% 7.41/1.50      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1,plain,
% 7.41/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_375,plain,
% 7.41/1.50      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.41/1.50      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_861,plain,
% 7.41/1.50      ( ~ l1_pre_topc(X0_54) | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_375]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3760,plain,
% 7.41/1.50      ( ~ l1_pre_topc(sK2) | u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_861]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_12,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.41/1.50      | ~ m1_pre_topc(X2,X1)
% 7.41/1.50      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | v2_struct_0(X0)
% 7.41/1.50      | v2_struct_0(X2)
% 7.41/1.50      | ~ l1_pre_topc(X1)
% 7.41/1.50      | ~ v2_pre_topc(X1) ),
% 7.41/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_883,plain,
% 7.41/1.50      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.50      | ~ m1_pre_topc(X2_54,X1_54)
% 7.41/1.50      | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54))
% 7.41/1.50      | v2_struct_0(X1_54)
% 7.41/1.50      | v2_struct_0(X0_54)
% 7.41/1.50      | v2_struct_0(X2_54)
% 7.41/1.50      | ~ l1_pre_topc(X1_54)
% 7.41/1.50      | ~ v2_pre_topc(X1_54) ),
% 7.41/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1455,plain,
% 7.41/1.51      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.41/1.51      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.41/1.51      | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54)) = iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X2_54) = iProver_top
% 7.41/1.51      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X1_54) != iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_883]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3587,plain,
% 7.41/1.51      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK2,sK3) = iProver_top
% 7.41/1.51      | v2_struct_0(sK0) = iProver_top
% 7.41/1.51      | v2_struct_0(sK2) = iProver_top
% 7.41/1.51      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.51      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.51      inference(superposition,[status(thm)],[c_3395,c_1455]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_20,negated_conjecture,
% 7.41/1.51      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.41/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_877,negated_conjecture,
% 7.41/1.51      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_20]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1461,plain,
% 7.41/1.51      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_21,negated_conjecture,
% 7.41/1.51      ( sK5 = sK6 ),
% 7.41/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_876,negated_conjecture,
% 7.41/1.51      ( sK5 = sK6 ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_21]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1515,plain,
% 7.41/1.51      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 7.41/1.51      inference(light_normalisation,[status(thm)],[c_1461,c_876]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_9,plain,
% 7.41/1.51      ( v1_tsep_1(X0,X1)
% 7.41/1.51      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.41/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.51      | ~ m1_pre_topc(X0,X1)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X1) ),
% 7.41/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_201,plain,
% 7.41/1.51      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.41/1.51      | v1_tsep_1(X0,X1)
% 7.41/1.51      | ~ m1_pre_topc(X0,X1)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X1) ),
% 7.41/1.51      inference(global_propositional_subsumption,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_9,c_11]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_202,plain,
% 7.41/1.51      ( v1_tsep_1(X0,X1)
% 7.41/1.51      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.41/1.51      | ~ m1_pre_topc(X0,X1)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X1) ),
% 7.41/1.51      inference(renaming,[status(thm)],[c_201]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_17,plain,
% 7.41/1.51      ( r1_tmap_1(X0,X1,X2,X3)
% 7.41/1.51      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.41/1.51      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.41/1.51      | ~ v1_tsep_1(X4,X0)
% 7.41/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.41/1.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_pre_topc(X4,X5)
% 7.41/1.51      | ~ m1_pre_topc(X4,X0)
% 7.41/1.51      | ~ m1_pre_topc(X0,X5)
% 7.41/1.51      | ~ v1_funct_1(X2)
% 7.41/1.51      | v2_struct_0(X5)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X4)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | ~ l1_pre_topc(X5)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X5)
% 7.41/1.51      | ~ v2_pre_topc(X1) ),
% 7.41/1.51      inference(cnf_transformation,[],[f99]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_26,negated_conjecture,
% 7.41/1.51      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.41/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_458,plain,
% 7.41/1.51      ( r1_tmap_1(X0,X1,X2,X3)
% 7.41/1.51      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.41/1.51      | ~ v1_tsep_1(X4,X0)
% 7.41/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.41/1.51      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_pre_topc(X4,X5)
% 7.41/1.51      | ~ m1_pre_topc(X4,X0)
% 7.41/1.51      | ~ m1_pre_topc(X0,X5)
% 7.41/1.51      | ~ v1_funct_1(X2)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | v2_struct_0(X5)
% 7.41/1.51      | v2_struct_0(X4)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ l1_pre_topc(X5)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X5)
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X0) != u1_struct_0(sK3)
% 7.41/1.51      | sK4 != X2 ),
% 7.41/1.51      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_459,plain,
% 7.41/1.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.41/1.51      | r1_tmap_1(X3,X1,sK4,X4)
% 7.41/1.51      | ~ v1_tsep_1(X0,X3)
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_pre_topc(X0,X2)
% 7.41/1.51      | ~ m1_pre_topc(X0,X3)
% 7.41/1.51      | ~ m1_pre_topc(X3,X2)
% 7.41/1.51      | ~ v1_funct_1(sK4)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X3)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ l1_pre_topc(X2)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X2)
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(unflattening,[status(thm)],[c_458]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_27,negated_conjecture,
% 7.41/1.51      ( v1_funct_1(sK4) ),
% 7.41/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_463,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X3,X2)
% 7.41/1.51      | ~ m1_pre_topc(X0,X3)
% 7.41/1.51      | ~ m1_pre_topc(X0,X2)
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.41/1.51      | ~ v1_tsep_1(X0,X3)
% 7.41/1.51      | r1_tmap_1(X3,X1,sK4,X4)
% 7.41/1.51      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X3)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ l1_pre_topc(X2)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X2)
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(global_propositional_subsumption,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_459,c_27]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_464,plain,
% 7.41/1.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.41/1.51      | r1_tmap_1(X3,X1,sK4,X4)
% 7.41/1.51      | ~ v1_tsep_1(X0,X3)
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_pre_topc(X0,X2)
% 7.41/1.51      | ~ m1_pre_topc(X0,X3)
% 7.41/1.51      | ~ m1_pre_topc(X3,X2)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | v2_struct_0(X3)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ l1_pre_topc(X2)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X2)
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(renaming,[status(thm)],[c_463]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_16,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.41/1.51      | ~ m1_pre_topc(X2,X0)
% 7.41/1.51      | m1_pre_topc(X2,X1)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X1) ),
% 7.41/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_507,plain,
% 7.41/1.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.41/1.51      | r1_tmap_1(X3,X1,sK4,X4)
% 7.41/1.51      | ~ v1_tsep_1(X0,X3)
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_pre_topc(X0,X3)
% 7.41/1.51      | ~ m1_pre_topc(X3,X2)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | v2_struct_0(X3)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ l1_pre_topc(X2)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X2)
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(forward_subsumption_resolution,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_464,c_16]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_530,plain,
% 7.41/1.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.41/1.51      | r1_tmap_1(X3,X1,sK4,X4)
% 7.41/1.51      | ~ v3_pre_topc(u1_struct_0(X5),X6)
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_pre_topc(X5,X6)
% 7.41/1.51      | ~ m1_pre_topc(X0,X3)
% 7.41/1.51      | ~ m1_pre_topc(X3,X2)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | v2_struct_0(X3)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | ~ l1_pre_topc(X6)
% 7.41/1.51      | ~ l1_pre_topc(X2)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X6)
% 7.41/1.51      | ~ v2_pre_topc(X2)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | X0 != X5
% 7.41/1.51      | X3 != X6
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(resolution_lifted,[status(thm)],[c_202,c_507]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_531,plain,
% 7.41/1.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.41/1.51      | r1_tmap_1(X3,X1,sK4,X4)
% 7.41/1.51      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_pre_topc(X0,X3)
% 7.41/1.51      | ~ m1_pre_topc(X3,X2)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | v2_struct_0(X3)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ l1_pre_topc(X2)
% 7.41/1.51      | ~ l1_pre_topc(X3)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X2)
% 7.41/1.51      | ~ v2_pre_topc(X3)
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(unflattening,[status(thm)],[c_530]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_0,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | v2_pre_topc(X0) ),
% 7.41/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.41/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_575,plain,
% 7.41/1.51      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.41/1.51      | r1_tmap_1(X3,X1,sK4,X4)
% 7.41/1.51      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.41/1.51      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.41/1.51      | ~ m1_pre_topc(X0,X3)
% 7.41/1.51      | ~ m1_pre_topc(X3,X2)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | v2_struct_0(X3)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ l1_pre_topc(X2)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X2)
% 7.41/1.51      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(forward_subsumption_resolution,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_531,c_0,c_3]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_860,plain,
% 7.41/1.51      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
% 7.41/1.51      | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
% 7.41/1.51      | ~ v3_pre_topc(u1_struct_0(X0_54),X3_54)
% 7.41/1.51      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 7.41/1.51      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 7.41/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 7.41/1.51      | ~ m1_pre_topc(X0_54,X3_54)
% 7.41/1.51      | ~ m1_pre_topc(X3_54,X2_54)
% 7.41/1.51      | v2_struct_0(X1_54)
% 7.41/1.51      | v2_struct_0(X0_54)
% 7.41/1.51      | v2_struct_0(X2_54)
% 7.41/1.51      | v2_struct_0(X3_54)
% 7.41/1.51      | ~ l1_pre_topc(X1_54)
% 7.41/1.51      | ~ l1_pre_topc(X2_54)
% 7.41/1.51      | ~ v2_pre_topc(X1_54)
% 7.41/1.51      | ~ v2_pre_topc(X2_54)
% 7.41/1.51      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_575]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1476,plain,
% 7.41/1.51      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 7.41/1.51      | u1_struct_0(X1_54) != u1_struct_0(sK3)
% 7.41/1.51      | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
% 7.41/1.51      | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(X2_54),X1_54) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.41/1.51      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.41/1.51      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 7.41/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X2_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X3_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | l1_pre_topc(X0_54) != iProver_top
% 7.41/1.51      | l1_pre_topc(X3_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X0_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X3_54) != iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2765,plain,
% 7.41/1.51      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.41/1.51      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.41/1.51      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.41/1.51      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.41/1.51      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X2_54) = iProver_top
% 7.41/1.51      | v2_struct_0(sK1) = iProver_top
% 7.41/1.51      | l1_pre_topc(X2_54) != iProver_top
% 7.41/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.41/1.51      | v2_pre_topc(X2_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.41/1.51      inference(equality_resolution,[status(thm)],[c_1476]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_34,negated_conjecture,
% 7.41/1.51      ( ~ v2_struct_0(sK1) ),
% 7.41/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_41,plain,
% 7.41/1.51      ( v2_struct_0(sK1) != iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_33,negated_conjecture,
% 7.41/1.51      ( v2_pre_topc(sK1) ),
% 7.41/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_42,plain,
% 7.41/1.51      ( v2_pre_topc(sK1) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_32,negated_conjecture,
% 7.41/1.51      ( l1_pre_topc(sK1) ),
% 7.41/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_43,plain,
% 7.41/1.51      ( l1_pre_topc(sK1) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3075,plain,
% 7.41/1.51      ( v2_pre_topc(X2_54) != iProver_top
% 7.41/1.51      | v2_struct_0(X2_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.41/1.51      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.41/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 7.41/1.51      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.41/1.51      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.41/1.51      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.41/1.51      | l1_pre_topc(X2_54) != iProver_top ),
% 7.41/1.51      inference(global_propositional_subsumption,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_2765,c_41,c_42,c_43]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3076,plain,
% 7.41/1.51      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.41/1.51      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.41/1.51      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.41/1.51      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.41/1.51      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X2_54) = iProver_top
% 7.41/1.51      | l1_pre_topc(X2_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X2_54) != iProver_top ),
% 7.41/1.51      inference(renaming,[status(thm)],[c_3075]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3093,plain,
% 7.41/1.51      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.41/1.51      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.41/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.41/1.51      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | v2_struct_0(sK3) = iProver_top
% 7.41/1.51      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X1_54) != iProver_top ),
% 7.41/1.51      inference(equality_resolution,[status(thm)],[c_3076]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_29,negated_conjecture,
% 7.41/1.51      ( ~ v2_struct_0(sK3) ),
% 7.41/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_46,plain,
% 7.41/1.51      ( v2_struct_0(sK3) != iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_25,negated_conjecture,
% 7.41/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.41/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_50,plain,
% 7.41/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3135,plain,
% 7.41/1.51      ( v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.41/1.51      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.41/1.51      | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.41/1.51      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.41/1.51      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X1_54) != iProver_top ),
% 7.41/1.51      inference(global_propositional_subsumption,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_3093,c_46,c_50]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3136,plain,
% 7.41/1.51      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.41/1.51      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.41/1.51      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.41/1.51      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.41/1.51      | v2_struct_0(X1_54) = iProver_top
% 7.41/1.51      | v2_struct_0(X0_54) = iProver_top
% 7.41/1.51      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X1_54) != iProver_top ),
% 7.41/1.51      inference(renaming,[status(thm)],[c_3135]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3152,plain,
% 7.41/1.51      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 7.41/1.51      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.41/1.51      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.41/1.51      | v2_struct_0(sK0) = iProver_top
% 7.41/1.51      | v2_struct_0(sK2) = iProver_top
% 7.41/1.51      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.51      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.51      inference(superposition,[status(thm)],[c_1515,c_3136]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_28,negated_conjecture,
% 7.41/1.51      ( m1_pre_topc(sK3,sK0) ),
% 7.41/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_47,plain,
% 7.41/1.51      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_23,negated_conjecture,
% 7.41/1.51      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.41/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_51,plain,
% 7.41/1.51      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_19,negated_conjecture,
% 7.41/1.51      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 7.41/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_54,plain,
% 7.41/1.51      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_22,negated_conjecture,
% 7.41/1.51      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.41/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_875,negated_conjecture,
% 7.41/1.51      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_22]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1462,plain,
% 7.41/1.51      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1500,plain,
% 7.41/1.51      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.41/1.51      inference(light_normalisation,[status(thm)],[c_1462,c_876]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3170,plain,
% 7.41/1.51      ( m1_pre_topc(sK2,sK3) != iProver_top
% 7.41/1.51      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top ),
% 7.41/1.51      inference(global_propositional_subsumption,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_3152,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1500]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3171,plain,
% 7.41/1.51      ( v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 7.41/1.51      inference(renaming,[status(thm)],[c_3170]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_3172,plain,
% 7.41/1.51      ( ~ v3_pre_topc(u1_struct_0(sK2),sK3) | ~ m1_pre_topc(sK2,sK3) ),
% 7.41/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3171]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2907,plain,
% 7.41/1.51      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.41/1.51      | ~ m1_pre_topc(sK2,sK2)
% 7.41/1.51      | ~ l1_pre_topc(sK2) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_884]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_889,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.51      | ~ l1_pre_topc(X1_54)
% 7.41/1.51      | l1_pre_topc(X0_54) ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1449,plain,
% 7.41/1.51      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.41/1.51      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.51      | l1_pre_topc(X0_54) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2774,plain,
% 7.41/1.51      ( l1_pre_topc(sK0) != iProver_top
% 7.41/1.51      | l1_pre_topc(sK2) = iProver_top ),
% 7.41/1.51      inference(superposition,[status(thm)],[c_1467,c_1449]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2784,plain,
% 7.41/1.51      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 7.41/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_2774]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_871,negated_conjecture,
% 7.41/1.51      ( m1_pre_topc(sK3,sK0) ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_28]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1465,plain,
% 7.41/1.51      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_871]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2773,plain,
% 7.41/1.51      ( l1_pre_topc(sK0) != iProver_top
% 7.41/1.51      | l1_pre_topc(sK3) = iProver_top ),
% 7.41/1.51      inference(superposition,[status(thm)],[c_1465,c_1449]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2783,plain,
% 7.41/1.51      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 7.41/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_2773]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2209,plain,
% 7.41/1.51      ( ~ m1_pre_topc(sK2,sK0)
% 7.41/1.51      | m1_pre_topc(sK2,sK3)
% 7.41/1.51      | ~ m1_pre_topc(sK3,sK0)
% 7.41/1.51      | v2_struct_0(sK0)
% 7.41/1.51      | v2_struct_0(sK2)
% 7.41/1.51      | v2_struct_0(sK3)
% 7.41/1.51      | ~ l1_pre_topc(sK0)
% 7.41/1.51      | ~ v2_pre_topc(sK0)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k1_tsep_1(sK0,sK2,sK3) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_1908]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1903,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0_54,sK0)
% 7.41/1.51      | m1_pre_topc(sK3,X0_54)
% 7.41/1.51      | ~ m1_pre_topc(sK3,sK0)
% 7.41/1.51      | v2_struct_0(X0_54)
% 7.41/1.51      | v2_struct_0(sK0)
% 7.41/1.51      | v2_struct_0(sK3)
% 7.41/1.51      | ~ l1_pre_topc(sK0)
% 7.41/1.51      | ~ v2_pre_topc(sK0)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != k1_tsep_1(sK0,sK3,X0_54) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_882]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2200,plain,
% 7.41/1.51      ( ~ m1_pre_topc(sK2,sK0)
% 7.41/1.51      | ~ m1_pre_topc(sK3,sK0)
% 7.41/1.51      | m1_pre_topc(sK3,sK2)
% 7.41/1.51      | v2_struct_0(sK0)
% 7.41/1.51      | v2_struct_0(sK2)
% 7.41/1.51      | v2_struct_0(sK3)
% 7.41/1.51      | ~ l1_pre_topc(sK0)
% 7.41/1.51      | ~ v2_pre_topc(sK0)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK3,sK2) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_1903]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_14,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.41/1.51      | ~ m1_pre_topc(X2,X1)
% 7.41/1.51      | ~ m1_pre_topc(X0,X2)
% 7.41/1.51      | v2_struct_0(X1)
% 7.41/1.51      | v2_struct_0(X0)
% 7.41/1.51      | v2_struct_0(X2)
% 7.41/1.51      | ~ l1_pre_topc(X1)
% 7.41/1.51      | ~ v2_pre_topc(X1)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
% 7.41/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_881,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.51      | ~ m1_pre_topc(X2_54,X1_54)
% 7.41/1.51      | ~ m1_pre_topc(X0_54,X2_54)
% 7.41/1.51      | v2_struct_0(X1_54)
% 7.41/1.51      | v2_struct_0(X0_54)
% 7.41/1.51      | v2_struct_0(X2_54)
% 7.41/1.51      | ~ l1_pre_topc(X1_54)
% 7.41/1.51      | ~ v2_pre_topc(X1_54)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) = k1_tsep_1(X1_54,X0_54,X2_54) ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_14]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1898,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0_54,sK0)
% 7.41/1.51      | ~ m1_pre_topc(sK2,X0_54)
% 7.41/1.51      | ~ m1_pre_topc(sK2,sK0)
% 7.41/1.51      | v2_struct_0(X0_54)
% 7.41/1.51      | v2_struct_0(sK0)
% 7.41/1.51      | v2_struct_0(sK2)
% 7.41/1.51      | ~ l1_pre_topc(sK0)
% 7.41/1.51      | ~ v2_pre_topc(sK0)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(sK0,sK2,X0_54) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_881]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2185,plain,
% 7.41/1.51      ( ~ m1_pre_topc(sK2,sK0)
% 7.41/1.51      | ~ m1_pre_topc(sK2,sK3)
% 7.41/1.51      | ~ m1_pre_topc(sK3,sK0)
% 7.41/1.51      | v2_struct_0(sK0)
% 7.41/1.51      | v2_struct_0(sK2)
% 7.41/1.51      | v2_struct_0(sK3)
% 7.41/1.51      | ~ l1_pre_topc(sK0)
% 7.41/1.51      | ~ v2_pre_topc(sK0)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK2,sK3) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_1898]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2186,plain,
% 7.41/1.51      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK0,sK2,sK3)
% 7.41/1.51      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.41/1.51      | v2_struct_0(sK0) = iProver_top
% 7.41/1.51      | v2_struct_0(sK2) = iProver_top
% 7.41/1.51      | v2_struct_0(sK3) = iProver_top
% 7.41/1.51      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.51      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_2185]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1893,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0_54,sK0)
% 7.41/1.51      | ~ m1_pre_topc(sK3,X0_54)
% 7.41/1.51      | ~ m1_pre_topc(sK3,sK0)
% 7.41/1.51      | v2_struct_0(X0_54)
% 7.41/1.51      | v2_struct_0(sK0)
% 7.41/1.51      | v2_struct_0(sK3)
% 7.41/1.51      | ~ l1_pre_topc(sK0)
% 7.41/1.51      | ~ v2_pre_topc(sK0)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(sK0,sK3,X0_54) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_881]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2172,plain,
% 7.41/1.51      ( ~ m1_pre_topc(sK2,sK0)
% 7.41/1.51      | ~ m1_pre_topc(sK3,sK0)
% 7.41/1.51      | ~ m1_pre_topc(sK3,sK2)
% 7.41/1.51      | v2_struct_0(sK0)
% 7.41/1.51      | v2_struct_0(sK2)
% 7.41/1.51      | v2_struct_0(sK3)
% 7.41/1.51      | ~ l1_pre_topc(sK0)
% 7.41/1.51      | ~ v2_pre_topc(sK0)
% 7.41/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2) ),
% 7.41/1.51      inference(instantiation,[status(thm)],[c_1893]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_2173,plain,
% 7.41/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2)
% 7.41/1.51      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.41/1.51      | m1_pre_topc(sK3,sK2) != iProver_top
% 7.41/1.51      | v2_struct_0(sK0) = iProver_top
% 7.41/1.51      | v2_struct_0(sK2) = iProver_top
% 7.41/1.51      | v2_struct_0(sK3) = iProver_top
% 7.41/1.51      | l1_pre_topc(sK0) != iProver_top
% 7.41/1.51      | v2_pre_topc(sK0) != iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_890,plain,
% 7.41/1.51      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.41/1.51      | ~ l1_pre_topc(X1_54)
% 7.41/1.51      | ~ v2_pre_topc(X1_54)
% 7.41/1.51      | v2_pre_topc(X0_54) ),
% 7.41/1.51      inference(subtyping,[status(esa)],[c_0]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1448,plain,
% 7.41/1.51      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.41/1.51      | l1_pre_topc(X1_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X1_54) != iProver_top
% 7.41/1.51      | v2_pre_topc(X0_54) = iProver_top ),
% 7.41/1.51      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1927,plain,
% 7.41/1.51      ( l1_pre_topc(sK0) != iProver_top
% 7.41/1.51      | v2_pre_topc(sK0) != iProver_top
% 7.41/1.51      | v2_pre_topc(sK2) = iProver_top ),
% 7.41/1.51      inference(superposition,[status(thm)],[c_1467,c_1448]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(c_1928,plain,
% 7.41/1.51      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK2) ),
% 7.41/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_1927]) ).
% 7.41/1.51  
% 7.41/1.51  cnf(contradiction,plain,
% 7.41/1.51      ( $false ),
% 7.41/1.51      inference(minisat,
% 7.41/1.51                [status(thm)],
% 7.41/1.51                [c_22943,c_13446,c_8196,c_5050,c_4993,c_3760,c_3587,
% 7.41/1.51                 c_3172,c_2907,c_2784,c_2774,c_2783,c_2212,c_2209,c_2200,
% 7.41/1.51                 c_2186,c_2173,c_1928,c_1877,c_47,c_28,c_46,c_29,c_45,
% 7.41/1.51                 c_30,c_44,c_31,c_40,c_35,c_39,c_36,c_38,c_37]) ).
% 7.41/1.51  
% 7.41/1.51  
% 7.41/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.41/1.51  
% 7.41/1.51  ------                               Statistics
% 7.41/1.51  
% 7.41/1.51  ------ General
% 7.41/1.51  
% 7.41/1.51  abstr_ref_over_cycles:                  0
% 7.41/1.51  abstr_ref_under_cycles:                 0
% 7.41/1.51  gc_basic_clause_elim:                   0
% 7.41/1.51  forced_gc_time:                         0
% 7.41/1.51  parsing_time:                           0.018
% 7.41/1.51  unif_index_cands_time:                  0.
% 7.41/1.51  unif_index_add_time:                    0.
% 7.41/1.51  orderings_time:                         0.
% 7.41/1.51  out_proof_time:                         0.014
% 7.41/1.51  total_time:                             0.754
% 7.41/1.51  num_of_symbols:                         60
% 7.41/1.51  num_of_terms:                           9246
% 7.41/1.51  
% 7.41/1.51  ------ Preprocessing
% 7.41/1.51  
% 7.41/1.51  num_of_splits:                          0
% 7.41/1.51  num_of_split_atoms:                     0
% 7.41/1.51  num_of_reused_defs:                     0
% 7.41/1.51  num_eq_ax_congr_red:                    18
% 7.41/1.51  num_of_sem_filtered_clauses:            1
% 7.41/1.51  num_of_subtypes:                        3
% 7.41/1.51  monotx_restored_types:                  0
% 7.41/1.51  sat_num_of_epr_types:                   0
% 7.41/1.51  sat_num_of_non_cyclic_types:            0
% 7.41/1.51  sat_guarded_non_collapsed_types:        0
% 7.41/1.51  num_pure_diseq_elim:                    0
% 7.41/1.51  simp_replaced_by:                       0
% 7.41/1.51  res_preprocessed:                       170
% 7.41/1.51  prep_upred:                             0
% 7.41/1.51  prep_unflattend:                        6
% 7.41/1.51  smt_new_axioms:                         0
% 7.41/1.51  pred_elim_cands:                        7
% 7.41/1.51  pred_elim:                              4
% 7.41/1.51  pred_elim_cl:                           5
% 7.41/1.51  pred_elim_cycles:                       6
% 7.41/1.51  merged_defs:                            0
% 7.41/1.51  merged_defs_ncl:                        0
% 7.41/1.51  bin_hyper_res:                          0
% 7.41/1.51  prep_cycles:                            4
% 7.41/1.51  pred_elim_time:                         0.016
% 7.41/1.51  splitting_time:                         0.
% 7.41/1.51  sem_filter_time:                        0.
% 7.41/1.51  monotx_time:                            0.
% 7.41/1.51  subtype_inf_time:                       0.001
% 7.41/1.51  
% 7.41/1.51  ------ Problem properties
% 7.41/1.51  
% 7.41/1.51  clauses:                                32
% 7.41/1.51  conjectures:                            17
% 7.41/1.51  epr:                                    15
% 7.41/1.51  horn:                                   26
% 7.41/1.51  ground:                                 17
% 7.41/1.51  unary:                                  17
% 7.41/1.51  binary:                                 1
% 7.41/1.51  lits:                                   118
% 7.41/1.51  lits_eq:                                10
% 7.41/1.51  fd_pure:                                0
% 7.41/1.51  fd_pseudo:                              0
% 7.41/1.51  fd_cond:                                0
% 7.41/1.51  fd_pseudo_cond:                         0
% 7.41/1.51  ac_symbols:                             0
% 7.41/1.51  
% 7.41/1.51  ------ Propositional Solver
% 7.41/1.51  
% 7.41/1.51  prop_solver_calls:                      29
% 7.41/1.51  prop_fast_solver_calls:                 2454
% 7.41/1.51  smt_solver_calls:                       0
% 7.41/1.51  smt_fast_solver_calls:                  0
% 7.41/1.51  prop_num_of_clauses:                    7102
% 7.41/1.51  prop_preprocess_simplified:             10417
% 7.41/1.51  prop_fo_subsumed:                       175
% 7.41/1.51  prop_solver_time:                       0.
% 7.41/1.51  smt_solver_time:                        0.
% 7.41/1.51  smt_fast_solver_time:                   0.
% 7.41/1.51  prop_fast_solver_time:                  0.
% 7.41/1.51  prop_unsat_core_time:                   0.001
% 7.41/1.51  
% 7.41/1.51  ------ QBF
% 7.41/1.51  
% 7.41/1.51  qbf_q_res:                              0
% 7.41/1.51  qbf_num_tautologies:                    0
% 7.41/1.51  qbf_prep_cycles:                        0
% 7.41/1.51  
% 7.41/1.51  ------ BMC1
% 7.41/1.51  
% 7.41/1.51  bmc1_current_bound:                     -1
% 7.41/1.51  bmc1_last_solved_bound:                 -1
% 7.41/1.51  bmc1_unsat_core_size:                   -1
% 7.41/1.51  bmc1_unsat_core_parents_size:           -1
% 7.41/1.51  bmc1_merge_next_fun:                    0
% 7.41/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.41/1.51  
% 7.41/1.51  ------ Instantiation
% 7.41/1.51  
% 7.41/1.51  inst_num_of_clauses:                    1575
% 7.41/1.51  inst_num_in_passive:                    427
% 7.41/1.51  inst_num_in_active:                     1014
% 7.41/1.51  inst_num_in_unprocessed:                133
% 7.41/1.51  inst_num_of_loops:                      1056
% 7.41/1.51  inst_num_of_learning_restarts:          0
% 7.41/1.51  inst_num_moves_active_passive:          37
% 7.41/1.51  inst_lit_activity:                      0
% 7.41/1.51  inst_lit_activity_moves:                0
% 7.41/1.51  inst_num_tautologies:                   0
% 7.41/1.51  inst_num_prop_implied:                  0
% 7.41/1.51  inst_num_existing_simplified:           0
% 7.41/1.51  inst_num_eq_res_simplified:             0
% 7.41/1.51  inst_num_child_elim:                    0
% 7.41/1.51  inst_num_of_dismatching_blockings:      205
% 7.41/1.51  inst_num_of_non_proper_insts:           1569
% 7.41/1.51  inst_num_of_duplicates:                 0
% 7.41/1.51  inst_inst_num_from_inst_to_res:         0
% 7.41/1.51  inst_dismatching_checking_time:         0.
% 7.41/1.51  
% 7.41/1.51  ------ Resolution
% 7.41/1.51  
% 7.41/1.51  res_num_of_clauses:                     0
% 7.41/1.51  res_num_in_passive:                     0
% 7.41/1.51  res_num_in_active:                      0
% 7.41/1.51  res_num_of_loops:                       174
% 7.41/1.51  res_forward_subset_subsumed:            125
% 7.41/1.51  res_backward_subset_subsumed:           2
% 7.41/1.51  res_forward_subsumed:                   0
% 7.41/1.51  res_backward_subsumed:                  0
% 7.41/1.51  res_forward_subsumption_resolution:     6
% 7.41/1.51  res_backward_subsumption_resolution:    0
% 7.41/1.51  res_clause_to_clause_subsumption:       4156
% 7.41/1.51  res_orphan_elimination:                 0
% 7.41/1.51  res_tautology_del:                      244
% 7.41/1.51  res_num_eq_res_simplified:              0
% 7.41/1.51  res_num_sel_changes:                    0
% 7.41/1.51  res_moves_from_active_to_pass:          0
% 7.41/1.51  
% 7.41/1.51  ------ Superposition
% 7.41/1.51  
% 7.41/1.51  sup_time_total:                         0.
% 7.41/1.51  sup_time_generating:                    0.
% 7.41/1.51  sup_time_sim_full:                      0.
% 7.41/1.51  sup_time_sim_immed:                     0.
% 7.41/1.51  
% 7.41/1.51  sup_num_of_clauses:                     809
% 7.41/1.51  sup_num_in_active:                      186
% 7.41/1.51  sup_num_in_passive:                     623
% 7.41/1.51  sup_num_of_loops:                       210
% 7.41/1.51  sup_fw_superposition:                   506
% 7.41/1.51  sup_bw_superposition:                   584
% 7.41/1.51  sup_immediate_simplified:               320
% 7.41/1.51  sup_given_eliminated:                   0
% 7.41/1.51  comparisons_done:                       0
% 7.41/1.51  comparisons_avoided:                    0
% 7.41/1.51  
% 7.41/1.51  ------ Simplifications
% 7.41/1.51  
% 7.41/1.51  
% 7.41/1.51  sim_fw_subset_subsumed:                 91
% 7.41/1.51  sim_bw_subset_subsumed:                 34
% 7.41/1.51  sim_fw_subsumed:                        89
% 7.41/1.51  sim_bw_subsumed:                        7
% 7.41/1.51  sim_fw_subsumption_res:                 3
% 7.41/1.51  sim_bw_subsumption_res:                 0
% 7.41/1.51  sim_tautology_del:                      24
% 7.41/1.51  sim_eq_tautology_del:                   10
% 7.41/1.51  sim_eq_res_simp:                        0
% 7.41/1.51  sim_fw_demodulated:                     2
% 7.41/1.51  sim_bw_demodulated:                     24
% 7.41/1.51  sim_light_normalised:                   174
% 7.41/1.51  sim_joinable_taut:                      0
% 7.41/1.51  sim_joinable_simp:                      0
% 7.41/1.51  sim_ac_normalised:                      0
% 7.41/1.51  sim_smt_subsumption:                    0
% 7.41/1.51  
%------------------------------------------------------------------------------
