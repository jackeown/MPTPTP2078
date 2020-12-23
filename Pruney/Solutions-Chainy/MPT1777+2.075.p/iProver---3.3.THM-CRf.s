%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:40 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  210 (1100 expanded)
%              Number of clauses        :  125 ( 296 expanded)
%              Number of leaves         :   22 ( 450 expanded)
%              Depth                    :   24
%              Number of atoms          : 1113 (14155 expanded)
%              Number of equality atoms :  276 (2131 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f49,f48,f47,f46,f45,f44,f43])).

fof(f77,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f81,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_13,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_201,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_13])).

cnf(c_396,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X1 != X2
    | u1_struct_0(X0) != k2_struct_0(X2) ),
    inference(resolution_lifted,[status(thm)],[c_7,c_201])).

cnf(c_397,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_787,plain,
    ( v1_tsep_1(X0_54,X1_54)
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | u1_struct_0(X0_54) != k2_struct_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_397])).

cnf(c_5237,plain,
    ( v1_tsep_1(sK2,X0_54)
    | ~ m1_pre_topc(sK2,X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54)
    | u1_struct_0(sK2) != k2_struct_0(X0_54) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_9040,plain,
    ( v1_tsep_1(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5237])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_808,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1319,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_797,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1328,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_811,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1316,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_2114,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_1316])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2352,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2114,c_40])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_381,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_788,plain,
    ( ~ l1_pre_topc(X0_54)
    | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_1337,plain,
    ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_2802,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2352,c_1337])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_209,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_3])).

cnf(c_210,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_789,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_210])).

cnf(c_1336,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_3685,plain,
    ( m1_pre_topc(X0_54,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2802,c_1336])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_801,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3546,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2802,c_801])).

cnf(c_3736,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X0_54,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3685,c_3546])).

cnf(c_3817,plain,
    ( m1_pre_topc(X0_54,sK3) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3736,c_40,c_2114])).

cnf(c_3818,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X0_54,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3817])).

cnf(c_3825,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_3818])).

cnf(c_3836,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3825,c_40,c_2114])).

cnf(c_4,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_810,plain,
    ( m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1317,plain,
    ( m1_pre_topc(X0_54,X1_54) = iProver_top
    | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_2258,plain,
    ( m1_pre_topc(X0_54,sK2) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_1317])).

cnf(c_2278,plain,
    ( m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(X0_54,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2258,c_40,c_2114])).

cnf(c_2279,plain,
    ( m1_pre_topc(X0_54,sK2) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2278])).

cnf(c_2286,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_2279])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_799,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1326,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_2113,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_1316])).

cnf(c_2425,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2286,c_40,c_2113])).

cnf(c_15,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_12,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X0,X2)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_423,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_15,c_12])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_445,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_423,c_3,c_16])).

cnf(c_786,plain,
    ( ~ v1_tsep_1(X0_54,X1_54)
    | v1_tsep_1(X0_54,X2_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_1339,plain,
    ( v1_tsep_1(X0_54,X1_54) != iProver_top
    | v1_tsep_1(X0_54,X2_54) = iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_5099,plain,
    ( v1_tsep_1(X0_54,sK2) != iProver_top
    | v1_tsep_1(X0_54,sK3) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2425,c_1339])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_812,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1315,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_1683,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_1315])).

cnf(c_7406,plain,
    ( v1_tsep_1(X0_54,sK2) != iProver_top
    | v1_tsep_1(X0_54,sK3) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5099,c_39,c_40,c_44,c_46,c_1683,c_2114])).

cnf(c_7418,plain,
    ( v1_tsep_1(sK2,sK2) != iProver_top
    | v1_tsep_1(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_7406])).

cnf(c_7435,plain,
    ( ~ v1_tsep_1(sK2,sK2)
    | v1_tsep_1(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7418])).

cnf(c_3833,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3825])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_805,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1322,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_21,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_804,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1383,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1322,c_804])).

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
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_534,plain,
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

cnf(c_535,plain,
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
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_539,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_27])).

cnf(c_540,plain,
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
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_583,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
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
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_540,c_16])).

cnf(c_784,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
    | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
    | ~ v1_tsep_1(X0_54,X3_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_1341,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(X1_54) != u1_struct_0(sK3)
    | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
    | v1_tsep_1(X2_54,X1_54) != iProver_top
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
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_2451,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK3)
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | v1_tsep_1(X1_54,X0_54) != iProver_top
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
    inference(equality_resolution,[status(thm)],[c_1341])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2572,plain,
    ( v2_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | v1_tsep_1(X1_54,X0_54) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_41,c_42,c_43])).

cnf(c_2573,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK3)
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | v1_tsep_1(X1_54,X0_54) != iProver_top
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
    inference(renaming,[status(thm)],[c_2572])).

cnf(c_2590,plain,
    ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v1_tsep_1(X0_54,sK3) != iProver_top
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
    inference(equality_resolution,[status(thm)],[c_2573])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2662,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v1_tsep_1(X0_54,sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2590,c_46,c_50])).

cnf(c_2663,plain,
    ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v1_tsep_1(X0_54,sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_2662])).

cnf(c_2679,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_2663])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_54,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_803,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1323,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_1364,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1323,c_804])).

cnf(c_3312,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2679,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1364])).

cnf(c_3313,plain,
    ( v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3312])).

cnf(c_3314,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3313])).

cnf(c_2732,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_2124,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2114])).

cnf(c_1684,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1683])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9040,c_7435,c_3833,c_3314,c_2802,c_2732,c_2124,c_1684,c_35,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:03:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.34/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.98  
% 3.34/0.98  ------  iProver source info
% 3.34/0.98  
% 3.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.98  git: non_committed_changes: false
% 3.34/0.98  git: last_make_outside_of_git: false
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     num_symb
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       true
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  ------ Parsing...
% 3.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.98  ------ Proving...
% 3.34/0.98  ------ Problem Properties 
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  clauses                                 29
% 3.34/0.98  conjectures                             17
% 3.34/0.98  EPR                                     17
% 3.34/0.98  Horn                                    26
% 3.34/0.98  unary                                   17
% 3.34/0.98  binary                                  2
% 3.34/0.98  lits                                    91
% 3.34/0.98  lits eq                                 8
% 3.34/0.98  fd_pure                                 0
% 3.34/0.98  fd_pseudo                               0
% 3.34/0.98  fd_cond                                 0
% 3.34/0.98  fd_pseudo_cond                          0
% 3.34/0.98  AC symbols                              0
% 3.34/0.98  
% 3.34/0.98  ------ Schedule dynamic 5 is on 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  Current options:
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     none
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       false
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ Proving...
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS status Theorem for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  fof(f7,axiom,(
% 3.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f24,plain,(
% 3.34/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f7])).
% 3.34/0.98  
% 3.34/0.98  fof(f25,plain,(
% 3.34/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.34/0.98    inference(flattening,[],[f24])).
% 3.34/0.98  
% 3.34/0.98  fof(f58,plain,(
% 3.34/0.98    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f25])).
% 3.34/0.98  
% 3.34/0.98  fof(f8,axiom,(
% 3.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f26,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f8])).
% 3.34/0.98  
% 3.34/0.98  fof(f27,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.34/0.98    inference(flattening,[],[f26])).
% 3.34/0.98  
% 3.34/0.98  fof(f40,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.34/0.98    inference(nnf_transformation,[],[f27])).
% 3.34/0.98  
% 3.34/0.98  fof(f41,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.34/0.98    inference(flattening,[],[f40])).
% 3.34/0.98  
% 3.34/0.98  fof(f60,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f41])).
% 3.34/0.98  
% 3.34/0.98  fof(f90,plain,(
% 3.34/0.98    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.34/0.98    inference(equality_resolution,[],[f60])).
% 3.34/0.98  
% 3.34/0.98  fof(f10,axiom,(
% 3.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f30,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f10])).
% 3.34/0.98  
% 3.34/0.98  fof(f64,plain,(
% 3.34/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f30])).
% 3.34/0.98  
% 3.34/0.98  fof(f11,axiom,(
% 3.34/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f31,plain,(
% 3.34/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f11])).
% 3.34/0.98  
% 3.34/0.98  fof(f65,plain,(
% 3.34/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f31])).
% 3.34/0.98  
% 3.34/0.98  fof(f15,conjecture,(
% 3.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f16,negated_conjecture,(
% 3.34/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.34/0.98    inference(negated_conjecture,[],[f15])).
% 3.34/0.98  
% 3.34/0.98  fof(f37,plain,(
% 3.34/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f38,plain,(
% 3.34/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.34/0.98    inference(flattening,[],[f37])).
% 3.34/0.98  
% 3.34/0.98  fof(f49,plain,(
% 3.34/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f48,plain,(
% 3.34/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f47,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f46,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f45,plain,(
% 3.34/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f44,plain,(
% 3.34/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f43,plain,(
% 3.34/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f50,plain,(
% 3.34/0.98    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f49,f48,f47,f46,f45,f44,f43])).
% 3.34/0.98  
% 3.34/0.98  fof(f77,plain,(
% 3.34/0.98    m1_pre_topc(sK2,sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f4,axiom,(
% 3.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f21,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f4])).
% 3.34/0.98  
% 3.34/0.98  fof(f54,plain,(
% 3.34/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f21])).
% 3.34/0.98  
% 3.34/0.98  fof(f72,plain,(
% 3.34/0.98    l1_pre_topc(sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f3,axiom,(
% 3.34/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f20,plain,(
% 3.34/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f3])).
% 3.34/0.98  
% 3.34/0.98  fof(f53,plain,(
% 3.34/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f20])).
% 3.34/0.98  
% 3.34/0.98  fof(f2,axiom,(
% 3.34/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f19,plain,(
% 3.34/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f2])).
% 3.34/0.98  
% 3.34/0.98  fof(f52,plain,(
% 3.34/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f19])).
% 3.34/0.98  
% 3.34/0.98  fof(f6,axiom,(
% 3.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f23,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f6])).
% 3.34/0.98  
% 3.34/0.98  fof(f39,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(nnf_transformation,[],[f23])).
% 3.34/0.98  
% 3.34/0.98  fof(f56,plain,(
% 3.34/0.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f39])).
% 3.34/0.98  
% 3.34/0.98  fof(f83,plain,(
% 3.34/0.98    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f5,axiom,(
% 3.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f22,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f5])).
% 3.34/0.98  
% 3.34/0.98  fof(f55,plain,(
% 3.34/0.98    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f22])).
% 3.34/0.98  
% 3.34/0.98  fof(f79,plain,(
% 3.34/0.98    m1_pre_topc(sK3,sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f12,axiom,(
% 3.34/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f32,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f12])).
% 3.34/0.98  
% 3.34/0.98  fof(f66,plain,(
% 3.34/0.98    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f32])).
% 3.34/0.98  
% 3.34/0.98  fof(f9,axiom,(
% 3.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f28,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f9])).
% 3.34/0.98  
% 3.34/0.98  fof(f29,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/0.98    inference(flattening,[],[f28])).
% 3.34/0.98  
% 3.34/0.98  fof(f62,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f29])).
% 3.34/0.98  
% 3.34/0.98  fof(f13,axiom,(
% 3.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f33,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f13])).
% 3.34/0.98  
% 3.34/0.98  fof(f34,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.34/0.98    inference(flattening,[],[f33])).
% 3.34/0.98  
% 3.34/0.98  fof(f67,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f34])).
% 3.34/0.98  
% 3.34/0.98  fof(f71,plain,(
% 3.34/0.98    v2_pre_topc(sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f76,plain,(
% 3.34/0.98    ~v2_struct_0(sK2)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f78,plain,(
% 3.34/0.98    ~v2_struct_0(sK3)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f1,axiom,(
% 3.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f17,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f1])).
% 3.34/0.98  
% 3.34/0.98  fof(f18,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.34/0.98    inference(flattening,[],[f17])).
% 3.34/0.98  
% 3.34/0.98  fof(f51,plain,(
% 3.34/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f18])).
% 3.34/0.98  
% 3.34/0.98  fof(f87,plain,(
% 3.34/0.98    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f86,plain,(
% 3.34/0.98    sK5 = sK6),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f14,axiom,(
% 3.34/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f35,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f14])).
% 3.34/0.98  
% 3.34/0.98  fof(f36,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/0.98    inference(flattening,[],[f35])).
% 3.34/0.98  
% 3.34/0.98  fof(f42,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/0.98    inference(nnf_transformation,[],[f36])).
% 3.34/0.98  
% 3.34/0.98  fof(f69,plain,(
% 3.34/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f42])).
% 3.34/0.98  
% 3.34/0.98  fof(f92,plain,(
% 3.34/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/0.98    inference(equality_resolution,[],[f69])).
% 3.34/0.98  
% 3.34/0.98  fof(f81,plain,(
% 3.34/0.98    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f80,plain,(
% 3.34/0.98    v1_funct_1(sK4)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f73,plain,(
% 3.34/0.98    ~v2_struct_0(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f74,plain,(
% 3.34/0.98    v2_pre_topc(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f75,plain,(
% 3.34/0.98    l1_pre_topc(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f82,plain,(
% 3.34/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f70,plain,(
% 3.34/0.98    ~v2_struct_0(sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f84,plain,(
% 3.34/0.98    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f88,plain,(
% 3.34/0.98    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f85,plain,(
% 3.34/0.98    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7,plain,
% 3.34/0.98      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.34/0.98      | ~ l1_pre_topc(X0)
% 3.34/0.98      | ~ v2_pre_topc(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9,plain,
% 3.34/0.98      ( v1_tsep_1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/0.98      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_13,plain,
% 3.34/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_201,plain,
% 3.34/0.98      ( v1_tsep_1(X0,X1)
% 3.34/0.98      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X1) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_9,c_13]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_396,plain,
% 3.34/0.98      ( v1_tsep_1(X0,X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X2)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X2)
% 3.34/0.98      | ~ v2_pre_topc(X1)
% 3.34/0.98      | X1 != X2
% 3.34/0.98      | u1_struct_0(X0) != k2_struct_0(X2) ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_201]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_397,plain,
% 3.34/0.98      ( v1_tsep_1(X0,X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X1)
% 3.34/0.98      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_396]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_787,plain,
% 3.34/0.98      ( v1_tsep_1(X0_54,X1_54)
% 3.34/0.98      | ~ m1_pre_topc(X0_54,X1_54)
% 3.34/0.98      | ~ l1_pre_topc(X1_54)
% 3.34/0.98      | ~ v2_pre_topc(X1_54)
% 3.34/0.98      | u1_struct_0(X0_54) != k2_struct_0(X1_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_397]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5237,plain,
% 3.34/0.98      ( v1_tsep_1(sK2,X0_54)
% 3.34/0.98      | ~ m1_pre_topc(sK2,X0_54)
% 3.34/0.98      | ~ l1_pre_topc(X0_54)
% 3.34/0.98      | ~ v2_pre_topc(X0_54)
% 3.34/0.98      | u1_struct_0(sK2) != k2_struct_0(X0_54) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_787]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9040,plain,
% 3.34/0.98      ( v1_tsep_1(sK2,sK2)
% 3.34/0.98      | ~ m1_pre_topc(sK2,sK2)
% 3.34/0.98      | ~ l1_pre_topc(sK2)
% 3.34/0.98      | ~ v2_pre_topc(sK2)
% 3.34/0.98      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_5237]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_14,plain,
% 3.34/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_808,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1319,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 3.34/0.98      | l1_pre_topc(X0_54) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_30,negated_conjecture,
% 3.34/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_797,negated_conjecture,
% 3.34/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_30]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1328,plain,
% 3.34/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_811,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.34/0.98      | ~ l1_pre_topc(X1_54)
% 3.34/0.98      | l1_pre_topc(X0_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1316,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.34/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.34/0.98      | l1_pre_topc(X0_54) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2114,plain,
% 3.34/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.34/0.98      | l1_pre_topc(sK2) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1328,c_1316]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_35,negated_conjecture,
% 3.34/0.98      ( l1_pre_topc(sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_40,plain,
% 3.34/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2352,plain,
% 3.34/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2114,c_40]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2,plain,
% 3.34/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1,plain,
% 3.34/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_381,plain,
% 3.34/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_788,plain,
% 3.34/0.98      ( ~ l1_pre_topc(X0_54) | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_381]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1337,plain,
% 3.34/0.98      ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
% 3.34/0.98      | l1_pre_topc(X0_54) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2802,plain,
% 3.34/0.98      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2352,c_1337]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.34/0.98      | ~ l1_pre_topc(X0)
% 3.34/0.98      | ~ l1_pre_topc(X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_209,plain,
% 3.34/0.98      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1) ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_6,c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_210,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.34/0.98      | ~ l1_pre_topc(X1) ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_209]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_789,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.34/0.98      | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
% 3.34/0.98      | ~ l1_pre_topc(X1_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_210]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1336,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) = iProver_top
% 3.34/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3685,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.34/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2802,c_1336]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_24,negated_conjecture,
% 3.34/0.98      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.34/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_801,negated_conjecture,
% 3.34/0.98      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3546,plain,
% 3.34/0.98      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_2802,c_801]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3736,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK3) = iProver_top
% 3.34/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_3685,c_3546]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3817,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,sK3) = iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_3736,c_40,c_2114]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3818,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK3) = iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_3817]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3825,plain,
% 3.34/0.98      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.34/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1319,c_3818]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3836,plain,
% 3.34/0.98      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_3825,c_40,c_2114]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4,plain,
% 3.34/0.98      ( m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.34/0.98      | ~ l1_pre_topc(X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_810,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,X1_54)
% 3.34/0.98      | ~ m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
% 3.34/0.98      | ~ l1_pre_topc(X1_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1317,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,X1_54) = iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) != iProver_top
% 3.34/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2258,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,sK2) = iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.34/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_801,c_1317]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2278,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,sK3) != iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK2) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2258,c_40,c_2114]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2279,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,sK2) = iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_2278]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2286,plain,
% 3.34/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.34/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1319,c_2279]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_28,negated_conjecture,
% 3.34/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_799,negated_conjecture,
% 3.34/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_28]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1326,plain,
% 3.34/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2113,plain,
% 3.34/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.34/0.98      | l1_pre_topc(sK3) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1326,c_1316]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2425,plain,
% 3.34/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2286,c_40,c_2113]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_15,plain,
% 3.34/0.98      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_12,plain,
% 3.34/0.98      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.34/0.98      | ~ v1_tsep_1(X0,X2)
% 3.34/0.98      | v1_tsep_1(X0,X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,X2)
% 3.34/0.98      | ~ m1_pre_topc(X1,X2)
% 3.34/0.98      | v2_struct_0(X2)
% 3.34/0.98      | v2_struct_0(X1)
% 3.34/0.98      | ~ l1_pre_topc(X2)
% 3.34/0.98      | ~ v2_pre_topc(X2) ),
% 3.34/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_423,plain,
% 3.34/0.98      ( ~ v1_tsep_1(X0,X1)
% 3.34/0.98      | v1_tsep_1(X0,X2)
% 3.34/0.98      | ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ m1_pre_topc(X2,X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,X2)
% 3.34/0.98      | v2_struct_0(X1)
% 3.34/0.98      | v2_struct_0(X2)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ l1_pre_topc(X2)
% 3.34/0.98      | ~ v2_pre_topc(X1) ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_15,c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_16,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ m1_pre_topc(X2,X0)
% 3.34/0.98      | m1_pre_topc(X2,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_445,plain,
% 3.34/0.98      ( ~ v1_tsep_1(X0,X1)
% 3.34/0.98      | v1_tsep_1(X0,X2)
% 3.34/0.98      | ~ m1_pre_topc(X2,X1)
% 3.34/0.98      | ~ m1_pre_topc(X0,X2)
% 3.34/0.98      | v2_struct_0(X1)
% 3.34/0.98      | v2_struct_0(X2)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X1) ),
% 3.34/0.98      inference(forward_subsumption_resolution,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_423,c_3,c_16]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_786,plain,
% 3.34/0.98      ( ~ v1_tsep_1(X0_54,X1_54)
% 3.34/0.98      | v1_tsep_1(X0_54,X2_54)
% 3.34/0.98      | ~ m1_pre_topc(X2_54,X1_54)
% 3.34/0.98      | ~ m1_pre_topc(X0_54,X2_54)
% 3.34/0.98      | v2_struct_0(X1_54)
% 3.34/0.98      | v2_struct_0(X2_54)
% 3.34/0.98      | ~ l1_pre_topc(X1_54)
% 3.34/0.98      | ~ v2_pre_topc(X1_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_445]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1339,plain,
% 3.34/0.98      ( v1_tsep_1(X0_54,X1_54) != iProver_top
% 3.34/0.98      | v1_tsep_1(X0_54,X2_54) = iProver_top
% 3.34/0.98      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.34/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.34/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.34/0.98      | v2_pre_topc(X1_54) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5099,plain,
% 3.34/0.98      ( v1_tsep_1(X0_54,sK2) != iProver_top
% 3.34/0.98      | v1_tsep_1(X0_54,sK3) = iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.34/0.98      | v2_struct_0(sK2) = iProver_top
% 3.34/0.98      | v2_struct_0(sK3) = iProver_top
% 3.34/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.34/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2425,c_1339]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_36,negated_conjecture,
% 3.34/0.98      ( v2_pre_topc(sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_39,plain,
% 3.34/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_31,negated_conjecture,
% 3.34/0.98      ( ~ v2_struct_0(sK2) ),
% 3.34/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_44,plain,
% 3.34/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_29,negated_conjecture,
% 3.34/0.98      ( ~ v2_struct_0(sK3) ),
% 3.34/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_46,plain,
% 3.34/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_0,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X1)
% 3.34/0.98      | v2_pre_topc(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_812,plain,
% 3.34/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.34/0.98      | ~ l1_pre_topc(X1_54)
% 3.34/0.98      | ~ v2_pre_topc(X1_54)
% 3.34/0.98      | v2_pre_topc(X0_54) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1315,plain,
% 3.34/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.34/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.34/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.34/0.98      | v2_pre_topc(X0_54) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1683,plain,
% 3.34/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.34/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.34/0.98      | v2_pre_topc(sK2) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1328,c_1315]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7406,plain,
% 3.34/0.98      ( v1_tsep_1(X0_54,sK2) != iProver_top
% 3.34/0.98      | v1_tsep_1(X0_54,sK3) = iProver_top
% 3.34/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_5099,c_39,c_40,c_44,c_46,c_1683,c_2114]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7418,plain,
% 3.34/0.98      ( v1_tsep_1(sK2,sK2) != iProver_top
% 3.34/0.98      | v1_tsep_1(sK2,sK3) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3836,c_7406]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7435,plain,
% 3.34/0.98      ( ~ v1_tsep_1(sK2,sK2) | v1_tsep_1(sK2,sK3) ),
% 3.34/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_7418]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3833,plain,
% 3.34/0.98      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 3.34/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3825]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_20,negated_conjecture,
% 3.34/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.34/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_805,negated_conjecture,
% 3.34/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1322,plain,
% 3.34/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_21,negated_conjecture,
% 3.34/0.98      ( sK5 = sK6 ),
% 3.34/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_804,negated_conjecture,
% 3.34/0.98      ( sK5 = sK6 ),
% 3.34/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1383,plain,
% 3.34/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_1322,c_804]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_17,plain,
% 3.34/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.34/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.34/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.34/0.98      | ~ v1_tsep_1(X4,X0)
% 3.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.34/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.34/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.34/0.98      | ~ m1_pre_topc(X4,X5)
% 3.34/0.98      | ~ m1_pre_topc(X4,X0)
% 3.34/0.98      | ~ m1_pre_topc(X0,X5)
% 3.34/0.98      | ~ v1_funct_1(X2)
% 3.34/0.98      | v2_struct_0(X5)
% 3.34/0.98      | v2_struct_0(X4)
% 3.34/0.98      | v2_struct_0(X1)
% 3.34/0.98      | v2_struct_0(X0)
% 3.34/0.98      | ~ l1_pre_topc(X5)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X5)
% 3.34/0.98      | ~ v2_pre_topc(X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_26,negated_conjecture,
% 3.34/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_534,plain,
% 3.34/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.34/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.34/0.98      | ~ v1_tsep_1(X4,X0)
% 3.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.34/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.34/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.34/0.98      | ~ m1_pre_topc(X4,X5)
% 3.34/0.98      | ~ m1_pre_topc(X4,X0)
% 3.34/0.98      | ~ m1_pre_topc(X0,X5)
% 3.34/0.98      | ~ v1_funct_1(X2)
% 3.34/0.98      | v2_struct_0(X1)
% 3.34/0.98      | v2_struct_0(X0)
% 3.34/0.98      | v2_struct_0(X5)
% 3.34/0.98      | v2_struct_0(X4)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ l1_pre_topc(X5)
% 3.34/0.98      | ~ v2_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X5)
% 3.34/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.34/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.34/0.98      | sK4 != X2 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_535,plain,
% 3.34/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.34/0.98      | r1_tmap_1(X3,X1,sK4,X4)
% 3.34/0.98      | ~ v1_tsep_1(X0,X3)
% 3.34/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.34/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.34/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.34/0.98      | ~ m1_pre_topc(X0,X2)
% 3.34/0.98      | ~ m1_pre_topc(X0,X3)
% 3.34/0.98      | ~ m1_pre_topc(X3,X2)
% 3.34/0.98      | ~ v1_funct_1(sK4)
% 3.34/0.98      | v2_struct_0(X1)
% 3.34/0.98      | v2_struct_0(X3)
% 3.34/0.98      | v2_struct_0(X2)
% 3.34/0.98      | v2_struct_0(X0)
% 3.34/0.98      | ~ l1_pre_topc(X1)
% 3.34/0.98      | ~ l1_pre_topc(X2)
% 3.34/0.98      | ~ v2_pre_topc(X1)
% 3.34/0.98      | ~ v2_pre_topc(X2)
% 3.34/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.34/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.34/0.99      inference(unflattening,[status(thm)],[c_534]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_27,negated_conjecture,
% 3.34/0.99      ( v1_funct_1(sK4) ),
% 3.34/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_539,plain,
% 3.34/0.99      ( ~ m1_pre_topc(X3,X2)
% 3.34/0.99      | ~ m1_pre_topc(X0,X3)
% 3.34/0.99      | ~ m1_pre_topc(X0,X2)
% 3.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.34/0.99      | ~ v1_tsep_1(X0,X3)
% 3.34/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.34/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.34/0.99      | v2_struct_0(X1)
% 3.34/0.99      | v2_struct_0(X3)
% 3.34/0.99      | v2_struct_0(X2)
% 3.34/0.99      | v2_struct_0(X0)
% 3.34/0.99      | ~ l1_pre_topc(X1)
% 3.34/0.99      | ~ l1_pre_topc(X2)
% 3.34/0.99      | ~ v2_pre_topc(X1)
% 3.34/0.99      | ~ v2_pre_topc(X2)
% 3.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.34/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_535,c_27]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_540,plain,
% 3.34/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.34/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.34/0.99      | ~ v1_tsep_1(X0,X3)
% 3.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.34/0.99      | ~ m1_pre_topc(X0,X2)
% 3.34/0.99      | ~ m1_pre_topc(X0,X3)
% 3.34/0.99      | ~ m1_pre_topc(X3,X2)
% 3.34/0.99      | v2_struct_0(X1)
% 3.34/0.99      | v2_struct_0(X2)
% 3.34/0.99      | v2_struct_0(X0)
% 3.34/0.99      | v2_struct_0(X3)
% 3.34/0.99      | ~ l1_pre_topc(X1)
% 3.34/0.99      | ~ l1_pre_topc(X2)
% 3.34/0.99      | ~ v2_pre_topc(X1)
% 3.34/0.99      | ~ v2_pre_topc(X2)
% 3.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.34/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.34/0.99      inference(renaming,[status(thm)],[c_539]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_583,plain,
% 3.34/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.34/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.34/0.99      | ~ v1_tsep_1(X0,X3)
% 3.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.34/0.99      | ~ m1_pre_topc(X0,X3)
% 3.34/0.99      | ~ m1_pre_topc(X3,X2)
% 3.34/0.99      | v2_struct_0(X1)
% 3.34/0.99      | v2_struct_0(X2)
% 3.34/0.99      | v2_struct_0(X0)
% 3.34/0.99      | v2_struct_0(X3)
% 3.34/0.99      | ~ l1_pre_topc(X1)
% 3.34/0.99      | ~ l1_pre_topc(X2)
% 3.34/0.99      | ~ v2_pre_topc(X1)
% 3.34/0.99      | ~ v2_pre_topc(X2)
% 3.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.34/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.34/0.99      inference(forward_subsumption_resolution,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_540,c_16]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_784,plain,
% 3.34/0.99      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
% 3.34/0.99      | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
% 3.34/0.99      | ~ v1_tsep_1(X0_54,X3_54)
% 3.34/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 3.34/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 3.34/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 3.34/0.99      | ~ m1_pre_topc(X0_54,X3_54)
% 3.34/0.99      | ~ m1_pre_topc(X3_54,X2_54)
% 3.34/0.99      | v2_struct_0(X1_54)
% 3.34/0.99      | v2_struct_0(X2_54)
% 3.34/0.99      | v2_struct_0(X0_54)
% 3.34/0.99      | v2_struct_0(X3_54)
% 3.34/0.99      | ~ l1_pre_topc(X1_54)
% 3.34/0.99      | ~ l1_pre_topc(X2_54)
% 3.34/0.99      | ~ v2_pre_topc(X1_54)
% 3.34/0.99      | ~ v2_pre_topc(X2_54)
% 3.34/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 3.34/0.99      | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
% 3.34/0.99      inference(subtyping,[status(esa)],[c_583]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1341,plain,
% 3.34/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.34/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK3)
% 3.34/0.99      | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
% 3.34/0.99      | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
% 3.34/0.99      | v1_tsep_1(X2_54,X1_54) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 3.34/0.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.34/0.99      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 3.34/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.34/0.99      | l1_pre_topc(X3_54) != iProver_top
% 3.34/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.34/0.99      | v2_pre_topc(X3_54) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2451,plain,
% 3.34/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 3.34/0.99      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 3.34/0.99      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 3.34/0.99      | v1_tsep_1(X1_54,X0_54) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 3.34/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.34/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.34/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.34/0.99      | v2_struct_0(sK1) = iProver_top
% 3.34/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.34/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.34/0.99      | v2_pre_topc(X2_54) != iProver_top
% 3.34/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.34/0.99      inference(equality_resolution,[status(thm)],[c_1341]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_34,negated_conjecture,
% 3.34/0.99      ( ~ v2_struct_0(sK1) ),
% 3.34/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_41,plain,
% 3.34/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_33,negated_conjecture,
% 3.34/0.99      ( v2_pre_topc(sK1) ),
% 3.34/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_42,plain,
% 3.34/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_32,negated_conjecture,
% 3.34/0.99      ( l1_pre_topc(sK1) ),
% 3.34/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_43,plain,
% 3.34/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2572,plain,
% 3.34/0.99      ( v2_pre_topc(X2_54) != iProver_top
% 3.34/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.34/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.34/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.34/0.99      | v1_tsep_1(X1_54,X0_54) != iProver_top
% 3.34/0.99      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 3.34/0.99      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 3.34/0.99      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 3.34/0.99      | l1_pre_topc(X2_54) != iProver_top ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_2451,c_41,c_42,c_43]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2573,plain,
% 3.34/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 3.34/0.99      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 3.34/0.99      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 3.34/0.99      | v1_tsep_1(X1_54,X0_54) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 3.34/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.34/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.34/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.34/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.34/0.99      | v2_pre_topc(X2_54) != iProver_top ),
% 3.34/0.99      inference(renaming,[status(thm)],[c_2572]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2590,plain,
% 3.34/0.99      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 3.34/0.99      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 3.34/0.99      | v1_tsep_1(X0_54,sK3) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 3.34/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.34/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.34/0.99      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.34/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.34/0.99      | v2_struct_0(sK3) = iProver_top
% 3.34/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.34/0.99      | v2_pre_topc(X1_54) != iProver_top ),
% 3.34/0.99      inference(equality_resolution,[status(thm)],[c_2573]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_25,negated_conjecture,
% 3.34/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.34/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_50,plain,
% 3.34/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2662,plain,
% 3.34/0.99      ( v2_struct_0(X0_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.99      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.34/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.34/0.99      | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 3.34/0.99      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 3.34/0.99      | v1_tsep_1(X0_54,sK3) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 3.34/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.34/0.99      | v2_pre_topc(X1_54) != iProver_top ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_2590,c_46,c_50]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2663,plain,
% 3.34/0.99      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 3.34/0.99      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 3.34/0.99      | v1_tsep_1(X0_54,sK3) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.34/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 3.34/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.34/0.99      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.34/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.34/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.34/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.34/0.99      | v2_pre_topc(X1_54) != iProver_top ),
% 3.34/0.99      inference(renaming,[status(thm)],[c_2662]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2679,plain,
% 3.34/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.34/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.34/0.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.34/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.34/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.34/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.34/0.99      | v2_struct_0(sK0) = iProver_top
% 3.34/0.99      | v2_struct_0(sK2) = iProver_top
% 3.34/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.34/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1383,c_2663]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_37,negated_conjecture,
% 3.34/0.99      ( ~ v2_struct_0(sK0) ),
% 3.34/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_38,plain,
% 3.34/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_47,plain,
% 3.34/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_23,negated_conjecture,
% 3.34/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.34/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_51,plain,
% 3.34/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_19,negated_conjecture,
% 3.34/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.34/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_54,plain,
% 3.34/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_22,negated_conjecture,
% 3.34/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.34/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_803,negated_conjecture,
% 3.34/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.34/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1323,plain,
% 3.34/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1364,plain,
% 3.34/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.34/0.99      inference(light_normalisation,[status(thm)],[c_1323,c_804]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3312,plain,
% 3.34/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.34/0.99      | v1_tsep_1(sK2,sK3) != iProver_top ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_2679,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1364]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3313,plain,
% 3.34/0.99      ( v1_tsep_1(sK2,sK3) != iProver_top
% 3.34/0.99      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 3.34/0.99      inference(renaming,[status(thm)],[c_3312]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3314,plain,
% 3.34/0.99      ( ~ v1_tsep_1(sK2,sK3) | ~ m1_pre_topc(sK2,sK3) ),
% 3.34/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3313]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2732,plain,
% 3.34/0.99      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_808]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2124,plain,
% 3.34/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.34/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2114]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1684,plain,
% 3.34/0.99      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK2) ),
% 3.34/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1683]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(contradiction,plain,
% 3.34/0.99      ( $false ),
% 3.34/0.99      inference(minisat,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_9040,c_7435,c_3833,c_3314,c_2802,c_2732,c_2124,c_1684,
% 3.34/0.99                 c_35,c_36]) ).
% 3.34/0.99  
% 3.34/0.99  
% 3.34/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.99  
% 3.34/0.99  ------                               Statistics
% 3.34/0.99  
% 3.34/0.99  ------ General
% 3.34/0.99  
% 3.34/0.99  abstr_ref_over_cycles:                  0
% 3.34/0.99  abstr_ref_under_cycles:                 0
% 3.34/0.99  gc_basic_clause_elim:                   0
% 3.34/0.99  forced_gc_time:                         0
% 3.34/0.99  parsing_time:                           0.009
% 3.34/0.99  unif_index_cands_time:                  0.
% 3.34/0.99  unif_index_add_time:                    0.
% 3.34/0.99  orderings_time:                         0.
% 3.34/0.99  out_proof_time:                         0.012
% 3.34/0.99  total_time:                             0.312
% 3.34/0.99  num_of_symbols:                         60
% 3.34/0.99  num_of_terms:                           4760
% 3.34/0.99  
% 3.34/0.99  ------ Preprocessing
% 3.34/0.99  
% 3.34/0.99  num_of_splits:                          0
% 3.34/0.99  num_of_split_atoms:                     0
% 3.34/0.99  num_of_reused_defs:                     0
% 3.34/0.99  num_eq_ax_congr_red:                    11
% 3.34/0.99  num_of_sem_filtered_clauses:            1
% 3.34/0.99  num_of_subtypes:                        3
% 3.34/0.99  monotx_restored_types:                  0
% 3.34/0.99  sat_num_of_epr_types:                   0
% 3.34/0.99  sat_num_of_non_cyclic_types:            0
% 3.34/0.99  sat_guarded_non_collapsed_types:        0
% 3.34/0.99  num_pure_diseq_elim:                    0
% 3.34/0.99  simp_replaced_by:                       0
% 3.34/0.99  res_preprocessed:                       158
% 3.34/0.99  prep_upred:                             0
% 3.34/0.99  prep_unflattend:                        3
% 3.34/0.99  smt_new_axioms:                         0
% 3.34/0.99  pred_elim_cands:                        7
% 3.34/0.99  pred_elim:                              5
% 3.34/0.99  pred_elim_cl:                           7
% 3.34/0.99  pred_elim_cycles:                       7
% 3.34/0.99  merged_defs:                            0
% 3.34/0.99  merged_defs_ncl:                        0
% 3.34/0.99  bin_hyper_res:                          0
% 3.34/0.99  prep_cycles:                            4
% 3.34/0.99  pred_elim_time:                         0.009
% 3.34/0.99  splitting_time:                         0.
% 3.34/0.99  sem_filter_time:                        0.
% 3.34/0.99  monotx_time:                            0.
% 3.34/0.99  subtype_inf_time:                       0.
% 3.34/0.99  
% 3.34/0.99  ------ Problem properties
% 3.34/0.99  
% 3.34/0.99  clauses:                                29
% 3.34/0.99  conjectures:                            17
% 3.34/0.99  epr:                                    17
% 3.34/0.99  horn:                                   26
% 3.34/0.99  ground:                                 17
% 3.34/0.99  unary:                                  17
% 3.34/0.99  binary:                                 2
% 3.34/0.99  lits:                                   91
% 3.34/0.99  lits_eq:                                8
% 3.34/0.99  fd_pure:                                0
% 3.34/0.99  fd_pseudo:                              0
% 3.34/0.99  fd_cond:                                0
% 3.34/0.99  fd_pseudo_cond:                         0
% 3.34/0.99  ac_symbols:                             0
% 3.34/0.99  
% 3.34/0.99  ------ Propositional Solver
% 3.34/0.99  
% 3.34/0.99  prop_solver_calls:                      30
% 3.34/0.99  prop_fast_solver_calls:                 1948
% 3.34/0.99  smt_solver_calls:                       0
% 3.34/0.99  smt_fast_solver_calls:                  0
% 3.34/0.99  prop_num_of_clauses:                    2491
% 3.34/0.99  prop_preprocess_simplified:             6453
% 3.34/0.99  prop_fo_subsumed:                       93
% 3.34/0.99  prop_solver_time:                       0.
% 3.34/0.99  smt_solver_time:                        0.
% 3.34/0.99  smt_fast_solver_time:                   0.
% 3.34/0.99  prop_fast_solver_time:                  0.
% 3.34/0.99  prop_unsat_core_time:                   0.
% 3.34/0.99  
% 3.34/0.99  ------ QBF
% 3.34/0.99  
% 3.34/0.99  qbf_q_res:                              0
% 3.34/0.99  qbf_num_tautologies:                    0
% 3.34/0.99  qbf_prep_cycles:                        0
% 3.34/0.99  
% 3.34/0.99  ------ BMC1
% 3.34/0.99  
% 3.34/0.99  bmc1_current_bound:                     -1
% 3.34/0.99  bmc1_last_solved_bound:                 -1
% 3.34/0.99  bmc1_unsat_core_size:                   -1
% 3.34/0.99  bmc1_unsat_core_parents_size:           -1
% 3.34/0.99  bmc1_merge_next_fun:                    0
% 3.34/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.99  
% 3.34/0.99  ------ Instantiation
% 3.34/0.99  
% 3.34/0.99  inst_num_of_clauses:                    778
% 3.34/0.99  inst_num_in_passive:                    51
% 3.34/0.99  inst_num_in_active:                     535
% 3.34/0.99  inst_num_in_unprocessed:                191
% 3.34/0.99  inst_num_of_loops:                      573
% 3.34/0.99  inst_num_of_learning_restarts:          0
% 3.34/0.99  inst_num_moves_active_passive:          31
% 3.34/0.99  inst_lit_activity:                      0
% 3.34/0.99  inst_lit_activity_moves:                0
% 3.34/0.99  inst_num_tautologies:                   0
% 3.34/0.99  inst_num_prop_implied:                  0
% 3.34/0.99  inst_num_existing_simplified:           0
% 3.34/0.99  inst_num_eq_res_simplified:             0
% 3.34/0.99  inst_num_child_elim:                    0
% 3.34/0.99  inst_num_of_dismatching_blockings:      480
% 3.34/0.99  inst_num_of_non_proper_insts:           1198
% 3.34/0.99  inst_num_of_duplicates:                 0
% 3.34/0.99  inst_inst_num_from_inst_to_res:         0
% 3.34/0.99  inst_dismatching_checking_time:         0.
% 3.34/0.99  
% 3.34/0.99  ------ Resolution
% 3.34/0.99  
% 3.34/0.99  res_num_of_clauses:                     0
% 3.34/0.99  res_num_in_passive:                     0
% 3.34/0.99  res_num_in_active:                      0
% 3.34/0.99  res_num_of_loops:                       162
% 3.34/0.99  res_forward_subset_subsumed:            213
% 3.34/0.99  res_backward_subset_subsumed:           2
% 3.34/0.99  res_forward_subsumed:                   0
% 3.34/0.99  res_backward_subsumed:                  0
% 3.34/0.99  res_forward_subsumption_resolution:     4
% 3.34/0.99  res_backward_subsumption_resolution:    0
% 3.34/0.99  res_clause_to_clause_subsumption:       643
% 3.34/0.99  res_orphan_elimination:                 0
% 3.34/0.99  res_tautology_del:                      223
% 3.34/0.99  res_num_eq_res_simplified:              0
% 3.34/0.99  res_num_sel_changes:                    0
% 3.34/0.99  res_moves_from_active_to_pass:          0
% 3.34/0.99  
% 3.34/0.99  ------ Superposition
% 3.34/0.99  
% 3.34/0.99  sup_time_total:                         0.
% 3.34/0.99  sup_time_generating:                    0.
% 3.34/0.99  sup_time_sim_full:                      0.
% 3.34/0.99  sup_time_sim_immed:                     0.
% 3.34/0.99  
% 3.34/0.99  sup_num_of_clauses:                     155
% 3.34/0.99  sup_num_in_active:                      103
% 3.34/0.99  sup_num_in_passive:                     52
% 3.34/0.99  sup_num_of_loops:                       114
% 3.34/0.99  sup_fw_superposition:                   120
% 3.34/0.99  sup_bw_superposition:                   85
% 3.34/0.99  sup_immediate_simplified:               64
% 3.34/0.99  sup_given_eliminated:                   0
% 3.34/0.99  comparisons_done:                       0
% 3.34/0.99  comparisons_avoided:                    0
% 3.34/0.99  
% 3.34/0.99  ------ Simplifications
% 3.34/0.99  
% 3.34/0.99  
% 3.34/0.99  sim_fw_subset_subsumed:                 24
% 3.34/0.99  sim_bw_subset_subsumed:                 15
% 3.34/0.99  sim_fw_subsumed:                        9
% 3.34/0.99  sim_bw_subsumed:                        0
% 3.34/0.99  sim_fw_subsumption_res:                 0
% 3.34/0.99  sim_bw_subsumption_res:                 0
% 3.34/0.99  sim_tautology_del:                      22
% 3.34/0.99  sim_eq_tautology_del:                   0
% 3.34/0.99  sim_eq_res_simp:                        0
% 3.34/0.99  sim_fw_demodulated:                     0
% 3.34/0.99  sim_bw_demodulated:                     11
% 3.34/0.99  sim_light_normalised:                   47
% 3.34/0.99  sim_joinable_taut:                      0
% 3.34/0.99  sim_joinable_simp:                      0
% 3.34/0.99  sim_ac_normalised:                      0
% 3.34/0.99  sim_smt_subsumption:                    0
% 3.34/0.99  
%------------------------------------------------------------------------------
