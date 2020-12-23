%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:39 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  203 (1060 expanded)
%              Number of clauses        :  117 ( 284 expanded)
%              Number of leaves         :   22 ( 433 expanded)
%              Depth                    :   23
%              Number of atoms          : 1105 (13628 expanded)
%              Number of equality atoms :  276 (2061 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f39,f50,f49,f48,f47,f46,f45,f44])).

fof(f78,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f30])).

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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f51])).

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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f82,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_816,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1326,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_805,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1335,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_820,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1322,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_1984,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_1322])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2277,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1984,c_40])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_383,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_796,plain,
    ( ~ l1_pre_topc(X0_54)
    | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_1344,plain,
    ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_2721,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2277,c_1344])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_212,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_3])).

cnf(c_213,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_797,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_213])).

cnf(c_1343,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_3312,plain,
    ( m1_pre_topc(X0_54,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2721,c_1343])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_809,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3295,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2721,c_809])).

cnf(c_3321,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X0_54,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3312,c_3295])).

cnf(c_3567,plain,
    ( m1_pre_topc(X0_54,sK3) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3321,c_40,c_1984])).

cnf(c_3568,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X0_54,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3567])).

cnf(c_3573,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_3568])).

cnf(c_3586,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_40,c_1984])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_818,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1324,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_2166,plain,
    ( m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(sK3,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_1324])).

cnf(c_2180,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_2166])).

cnf(c_2393,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2180,c_40,c_1984])).

cnf(c_15,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

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
    inference(cnf_transformation,[],[f63])).

cnf(c_425,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_447,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_425,c_3,c_16])).

cnf(c_794,plain,
    ( ~ v1_tsep_1(X0_54,X1_54)
    | v1_tsep_1(X0_54,X2_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_1346,plain,
    ( v1_tsep_1(X0_54,X1_54) != iProver_top
    | v1_tsep_1(X0_54,X2_54) = iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_4667,plain,
    ( v1_tsep_1(X0_54,sK2) != iProver_top
    | v1_tsep_1(X0_54,sK3) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_1346])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_821,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1321,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_1605,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_1321])).

cnf(c_15359,plain,
    ( v1_tsep_1(X0_54,sK2) != iProver_top
    | v1_tsep_1(X0_54,sK3) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4667,c_39,c_40,c_44,c_46,c_1605,c_1984])).

cnf(c_15372,plain,
    ( v1_tsep_1(sK2,sK2) != iProver_top
    | v1_tsep_1(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3586,c_15359])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f91])).

cnf(c_13,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_203,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_13])).

cnf(c_398,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X1 != X2
    | u1_struct_0(X0) != k2_struct_0(X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_203])).

cnf(c_399,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_795,plain,
    ( v1_tsep_1(X0_54,X1_54)
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | u1_struct_0(X0_54) != k2_struct_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_399])).

cnf(c_4312,plain,
    ( v1_tsep_1(sK2,X0_54)
    | ~ m1_pre_topc(sK2,X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54)
    | u1_struct_0(sK2) != k2_struct_0(X0_54) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_9458,plain,
    ( v1_tsep_1(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4312])).

cnf(c_9459,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | v1_tsep_1(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9458])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_813,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1329,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_21,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_812,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1350,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1329,c_812])).

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
    inference(cnf_transformation,[],[f93])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_536,plain,
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

cnf(c_537,plain,
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
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_541,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_27])).

cnf(c_542,plain,
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
    inference(renaming,[status(thm)],[c_541])).

cnf(c_585,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_542,c_16])).

cnf(c_792,plain,
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
    inference(subtyping,[status(esa)],[c_585])).

cnf(c_1348,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_2400,plain,
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
    inference(equality_resolution,[status(thm)],[c_1348])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2462,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2400,c_41,c_42,c_43])).

cnf(c_2463,plain,
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
    inference(renaming,[status(thm)],[c_2462])).

cnf(c_2466,plain,
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
    inference(equality_resolution,[status(thm)],[c_2463])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2544,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2466,c_46,c_50])).

cnf(c_2545,plain,
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
    inference(renaming,[status(thm)],[c_2544])).

cnf(c_2550,plain,
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
    inference(superposition,[status(thm)],[c_1350,c_2545])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_54,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_811,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1330,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_1349,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1330,c_812])).

cnf(c_3039,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2550,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1349])).

cnf(c_3040,plain,
    ( v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3039])).

cnf(c_2599,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_2600,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2599])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15372,c_9459,c_3573,c_3040,c_2721,c_2600,c_1984,c_1605,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:00:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.78/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.49  
% 7.78/1.49  ------  iProver source info
% 7.78/1.49  
% 7.78/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.49  git: non_committed_changes: false
% 7.78/1.49  git: last_make_outside_of_git: false
% 7.78/1.49  
% 7.78/1.49  ------ 
% 7.78/1.49  
% 7.78/1.49  ------ Input Options
% 7.78/1.49  
% 7.78/1.49  --out_options                           all
% 7.78/1.49  --tptp_safe_out                         true
% 7.78/1.49  --problem_path                          ""
% 7.78/1.49  --include_path                          ""
% 7.78/1.49  --clausifier                            res/vclausify_rel
% 7.78/1.49  --clausifier_options                    ""
% 7.78/1.49  --stdin                                 false
% 7.78/1.49  --stats_out                             all
% 7.78/1.49  
% 7.78/1.49  ------ General Options
% 7.78/1.49  
% 7.78/1.49  --fof                                   false
% 7.78/1.49  --time_out_real                         305.
% 7.78/1.49  --time_out_virtual                      -1.
% 7.78/1.49  --symbol_type_check                     false
% 7.78/1.49  --clausify_out                          false
% 7.78/1.49  --sig_cnt_out                           false
% 7.78/1.49  --trig_cnt_out                          false
% 7.78/1.49  --trig_cnt_out_tolerance                1.
% 7.78/1.49  --trig_cnt_out_sk_spl                   false
% 7.78/1.49  --abstr_cl_out                          false
% 7.78/1.49  
% 7.78/1.49  ------ Global Options
% 7.78/1.49  
% 7.78/1.49  --schedule                              default
% 7.78/1.49  --add_important_lit                     false
% 7.78/1.49  --prop_solver_per_cl                    1000
% 7.78/1.49  --min_unsat_core                        false
% 7.78/1.49  --soft_assumptions                      false
% 7.78/1.49  --soft_lemma_size                       3
% 7.78/1.49  --prop_impl_unit_size                   0
% 7.78/1.49  --prop_impl_unit                        []
% 7.78/1.49  --share_sel_clauses                     true
% 7.78/1.49  --reset_solvers                         false
% 7.78/1.49  --bc_imp_inh                            [conj_cone]
% 7.78/1.49  --conj_cone_tolerance                   3.
% 7.78/1.49  --extra_neg_conj                        none
% 7.78/1.49  --large_theory_mode                     true
% 7.78/1.49  --prolific_symb_bound                   200
% 7.78/1.49  --lt_threshold                          2000
% 7.78/1.49  --clause_weak_htbl                      true
% 7.78/1.49  --gc_record_bc_elim                     false
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing Options
% 7.78/1.49  
% 7.78/1.49  --preprocessing_flag                    true
% 7.78/1.49  --time_out_prep_mult                    0.1
% 7.78/1.49  --splitting_mode                        input
% 7.78/1.49  --splitting_grd                         true
% 7.78/1.49  --splitting_cvd                         false
% 7.78/1.49  --splitting_cvd_svl                     false
% 7.78/1.49  --splitting_nvd                         32
% 7.78/1.49  --sub_typing                            true
% 7.78/1.49  --prep_gs_sim                           true
% 7.78/1.49  --prep_unflatten                        true
% 7.78/1.49  --prep_res_sim                          true
% 7.78/1.49  --prep_upred                            true
% 7.78/1.49  --prep_sem_filter                       exhaustive
% 7.78/1.49  --prep_sem_filter_out                   false
% 7.78/1.49  --pred_elim                             true
% 7.78/1.49  --res_sim_input                         true
% 7.78/1.49  --eq_ax_congr_red                       true
% 7.78/1.49  --pure_diseq_elim                       true
% 7.78/1.49  --brand_transform                       false
% 7.78/1.49  --non_eq_to_eq                          false
% 7.78/1.49  --prep_def_merge                        true
% 7.78/1.49  --prep_def_merge_prop_impl              false
% 7.78/1.49  --prep_def_merge_mbd                    true
% 7.78/1.49  --prep_def_merge_tr_red                 false
% 7.78/1.49  --prep_def_merge_tr_cl                  false
% 7.78/1.49  --smt_preprocessing                     true
% 7.78/1.49  --smt_ac_axioms                         fast
% 7.78/1.49  --preprocessed_out                      false
% 7.78/1.49  --preprocessed_stats                    false
% 7.78/1.49  
% 7.78/1.49  ------ Abstraction refinement Options
% 7.78/1.49  
% 7.78/1.49  --abstr_ref                             []
% 7.78/1.49  --abstr_ref_prep                        false
% 7.78/1.49  --abstr_ref_until_sat                   false
% 7.78/1.49  --abstr_ref_sig_restrict                funpre
% 7.78/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.49  --abstr_ref_under                       []
% 7.78/1.49  
% 7.78/1.49  ------ SAT Options
% 7.78/1.49  
% 7.78/1.49  --sat_mode                              false
% 7.78/1.49  --sat_fm_restart_options                ""
% 7.78/1.49  --sat_gr_def                            false
% 7.78/1.49  --sat_epr_types                         true
% 7.78/1.49  --sat_non_cyclic_types                  false
% 7.78/1.49  --sat_finite_models                     false
% 7.78/1.49  --sat_fm_lemmas                         false
% 7.78/1.49  --sat_fm_prep                           false
% 7.78/1.49  --sat_fm_uc_incr                        true
% 7.78/1.49  --sat_out_model                         small
% 7.78/1.49  --sat_out_clauses                       false
% 7.78/1.49  
% 7.78/1.49  ------ QBF Options
% 7.78/1.49  
% 7.78/1.49  --qbf_mode                              false
% 7.78/1.49  --qbf_elim_univ                         false
% 7.78/1.49  --qbf_dom_inst                          none
% 7.78/1.49  --qbf_dom_pre_inst                      false
% 7.78/1.49  --qbf_sk_in                             false
% 7.78/1.49  --qbf_pred_elim                         true
% 7.78/1.49  --qbf_split                             512
% 7.78/1.49  
% 7.78/1.49  ------ BMC1 Options
% 7.78/1.49  
% 7.78/1.49  --bmc1_incremental                      false
% 7.78/1.49  --bmc1_axioms                           reachable_all
% 7.78/1.49  --bmc1_min_bound                        0
% 7.78/1.49  --bmc1_max_bound                        -1
% 7.78/1.49  --bmc1_max_bound_default                -1
% 7.78/1.49  --bmc1_symbol_reachability              true
% 7.78/1.49  --bmc1_property_lemmas                  false
% 7.78/1.49  --bmc1_k_induction                      false
% 7.78/1.49  --bmc1_non_equiv_states                 false
% 7.78/1.49  --bmc1_deadlock                         false
% 7.78/1.49  --bmc1_ucm                              false
% 7.78/1.49  --bmc1_add_unsat_core                   none
% 7.78/1.49  --bmc1_unsat_core_children              false
% 7.78/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.49  --bmc1_out_stat                         full
% 7.78/1.49  --bmc1_ground_init                      false
% 7.78/1.49  --bmc1_pre_inst_next_state              false
% 7.78/1.49  --bmc1_pre_inst_state                   false
% 7.78/1.49  --bmc1_pre_inst_reach_state             false
% 7.78/1.49  --bmc1_out_unsat_core                   false
% 7.78/1.49  --bmc1_aig_witness_out                  false
% 7.78/1.49  --bmc1_verbose                          false
% 7.78/1.49  --bmc1_dump_clauses_tptp                false
% 7.78/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.49  --bmc1_dump_file                        -
% 7.78/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.49  --bmc1_ucm_extend_mode                  1
% 7.78/1.49  --bmc1_ucm_init_mode                    2
% 7.78/1.49  --bmc1_ucm_cone_mode                    none
% 7.78/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.49  --bmc1_ucm_relax_model                  4
% 7.78/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.49  --bmc1_ucm_layered_model                none
% 7.78/1.49  --bmc1_ucm_max_lemma_size               10
% 7.78/1.49  
% 7.78/1.49  ------ AIG Options
% 7.78/1.49  
% 7.78/1.49  --aig_mode                              false
% 7.78/1.49  
% 7.78/1.49  ------ Instantiation Options
% 7.78/1.49  
% 7.78/1.49  --instantiation_flag                    true
% 7.78/1.49  --inst_sos_flag                         true
% 7.78/1.49  --inst_sos_phase                        true
% 7.78/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.49  --inst_lit_sel_side                     num_symb
% 7.78/1.49  --inst_solver_per_active                1400
% 7.78/1.49  --inst_solver_calls_frac                1.
% 7.78/1.49  --inst_passive_queue_type               priority_queues
% 7.78/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.49  --inst_passive_queues_freq              [25;2]
% 7.78/1.49  --inst_dismatching                      true
% 7.78/1.49  --inst_eager_unprocessed_to_passive     true
% 7.78/1.49  --inst_prop_sim_given                   true
% 7.78/1.49  --inst_prop_sim_new                     false
% 7.78/1.49  --inst_subs_new                         false
% 7.78/1.49  --inst_eq_res_simp                      false
% 7.78/1.49  --inst_subs_given                       false
% 7.78/1.49  --inst_orphan_elimination               true
% 7.78/1.49  --inst_learning_loop_flag               true
% 7.78/1.49  --inst_learning_start                   3000
% 7.78/1.49  --inst_learning_factor                  2
% 7.78/1.49  --inst_start_prop_sim_after_learn       3
% 7.78/1.49  --inst_sel_renew                        solver
% 7.78/1.49  --inst_lit_activity_flag                true
% 7.78/1.49  --inst_restr_to_given                   false
% 7.78/1.49  --inst_activity_threshold               500
% 7.78/1.49  --inst_out_proof                        true
% 7.78/1.49  
% 7.78/1.49  ------ Resolution Options
% 7.78/1.49  
% 7.78/1.49  --resolution_flag                       true
% 7.78/1.49  --res_lit_sel                           adaptive
% 7.78/1.49  --res_lit_sel_side                      none
% 7.78/1.49  --res_ordering                          kbo
% 7.78/1.49  --res_to_prop_solver                    active
% 7.78/1.49  --res_prop_simpl_new                    false
% 7.78/1.49  --res_prop_simpl_given                  true
% 7.78/1.49  --res_passive_queue_type                priority_queues
% 7.78/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.49  --res_passive_queues_freq               [15;5]
% 7.78/1.49  --res_forward_subs                      full
% 7.78/1.49  --res_backward_subs                     full
% 7.78/1.49  --res_forward_subs_resolution           true
% 7.78/1.49  --res_backward_subs_resolution          true
% 7.78/1.49  --res_orphan_elimination                true
% 7.78/1.49  --res_time_limit                        2.
% 7.78/1.49  --res_out_proof                         true
% 7.78/1.49  
% 7.78/1.49  ------ Superposition Options
% 7.78/1.49  
% 7.78/1.49  --superposition_flag                    true
% 7.78/1.49  --sup_passive_queue_type                priority_queues
% 7.78/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.49  --demod_completeness_check              fast
% 7.78/1.49  --demod_use_ground                      true
% 7.78/1.49  --sup_to_prop_solver                    passive
% 7.78/1.49  --sup_prop_simpl_new                    true
% 7.78/1.49  --sup_prop_simpl_given                  true
% 7.78/1.49  --sup_fun_splitting                     true
% 7.78/1.49  --sup_smt_interval                      50000
% 7.78/1.49  
% 7.78/1.49  ------ Superposition Simplification Setup
% 7.78/1.49  
% 7.78/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.49  --sup_immed_triv                        [TrivRules]
% 7.78/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_immed_bw_main                     []
% 7.78/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_input_bw                          []
% 7.78/1.49  
% 7.78/1.49  ------ Combination Options
% 7.78/1.49  
% 7.78/1.49  --comb_res_mult                         3
% 7.78/1.49  --comb_sup_mult                         2
% 7.78/1.49  --comb_inst_mult                        10
% 7.78/1.49  
% 7.78/1.49  ------ Debug Options
% 7.78/1.49  
% 7.78/1.49  --dbg_backtrace                         false
% 7.78/1.49  --dbg_dump_prop_clauses                 false
% 7.78/1.49  --dbg_dump_prop_clauses_file            -
% 7.78/1.49  --dbg_out_stat                          false
% 7.78/1.49  ------ Parsing...
% 7.78/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.49  ------ Proving...
% 7.78/1.49  ------ Problem Properties 
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  clauses                                 30
% 7.78/1.49  conjectures                             17
% 7.78/1.49  EPR                                     17
% 7.78/1.49  Horn                                    27
% 7.78/1.49  unary                                   17
% 7.78/1.49  binary                                  2
% 7.78/1.49  lits                                    95
% 7.78/1.49  lits eq                                 8
% 7.78/1.49  fd_pure                                 0
% 7.78/1.49  fd_pseudo                               0
% 7.78/1.49  fd_cond                                 0
% 7.78/1.49  fd_pseudo_cond                          0
% 7.78/1.49  AC symbols                              0
% 7.78/1.49  
% 7.78/1.49  ------ Schedule dynamic 5 is on 
% 7.78/1.49  
% 7.78/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ 
% 7.78/1.49  Current options:
% 7.78/1.49  ------ 
% 7.78/1.49  
% 7.78/1.49  ------ Input Options
% 7.78/1.49  
% 7.78/1.49  --out_options                           all
% 7.78/1.49  --tptp_safe_out                         true
% 7.78/1.49  --problem_path                          ""
% 7.78/1.49  --include_path                          ""
% 7.78/1.49  --clausifier                            res/vclausify_rel
% 7.78/1.49  --clausifier_options                    ""
% 7.78/1.49  --stdin                                 false
% 7.78/1.49  --stats_out                             all
% 7.78/1.49  
% 7.78/1.49  ------ General Options
% 7.78/1.49  
% 7.78/1.49  --fof                                   false
% 7.78/1.49  --time_out_real                         305.
% 7.78/1.49  --time_out_virtual                      -1.
% 7.78/1.49  --symbol_type_check                     false
% 7.78/1.49  --clausify_out                          false
% 7.78/1.49  --sig_cnt_out                           false
% 7.78/1.49  --trig_cnt_out                          false
% 7.78/1.49  --trig_cnt_out_tolerance                1.
% 7.78/1.49  --trig_cnt_out_sk_spl                   false
% 7.78/1.49  --abstr_cl_out                          false
% 7.78/1.49  
% 7.78/1.49  ------ Global Options
% 7.78/1.49  
% 7.78/1.49  --schedule                              default
% 7.78/1.49  --add_important_lit                     false
% 7.78/1.49  --prop_solver_per_cl                    1000
% 7.78/1.49  --min_unsat_core                        false
% 7.78/1.49  --soft_assumptions                      false
% 7.78/1.49  --soft_lemma_size                       3
% 7.78/1.49  --prop_impl_unit_size                   0
% 7.78/1.49  --prop_impl_unit                        []
% 7.78/1.49  --share_sel_clauses                     true
% 7.78/1.49  --reset_solvers                         false
% 7.78/1.49  --bc_imp_inh                            [conj_cone]
% 7.78/1.49  --conj_cone_tolerance                   3.
% 7.78/1.49  --extra_neg_conj                        none
% 7.78/1.49  --large_theory_mode                     true
% 7.78/1.49  --prolific_symb_bound                   200
% 7.78/1.49  --lt_threshold                          2000
% 7.78/1.49  --clause_weak_htbl                      true
% 7.78/1.49  --gc_record_bc_elim                     false
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing Options
% 7.78/1.49  
% 7.78/1.49  --preprocessing_flag                    true
% 7.78/1.49  --time_out_prep_mult                    0.1
% 7.78/1.49  --splitting_mode                        input
% 7.78/1.49  --splitting_grd                         true
% 7.78/1.49  --splitting_cvd                         false
% 7.78/1.49  --splitting_cvd_svl                     false
% 7.78/1.49  --splitting_nvd                         32
% 7.78/1.49  --sub_typing                            true
% 7.78/1.49  --prep_gs_sim                           true
% 7.78/1.49  --prep_unflatten                        true
% 7.78/1.49  --prep_res_sim                          true
% 7.78/1.49  --prep_upred                            true
% 7.78/1.49  --prep_sem_filter                       exhaustive
% 7.78/1.49  --prep_sem_filter_out                   false
% 7.78/1.49  --pred_elim                             true
% 7.78/1.49  --res_sim_input                         true
% 7.78/1.49  --eq_ax_congr_red                       true
% 7.78/1.49  --pure_diseq_elim                       true
% 7.78/1.49  --brand_transform                       false
% 7.78/1.49  --non_eq_to_eq                          false
% 7.78/1.49  --prep_def_merge                        true
% 7.78/1.49  --prep_def_merge_prop_impl              false
% 7.78/1.49  --prep_def_merge_mbd                    true
% 7.78/1.49  --prep_def_merge_tr_red                 false
% 7.78/1.49  --prep_def_merge_tr_cl                  false
% 7.78/1.49  --smt_preprocessing                     true
% 7.78/1.49  --smt_ac_axioms                         fast
% 7.78/1.49  --preprocessed_out                      false
% 7.78/1.49  --preprocessed_stats                    false
% 7.78/1.49  
% 7.78/1.49  ------ Abstraction refinement Options
% 7.78/1.49  
% 7.78/1.49  --abstr_ref                             []
% 7.78/1.49  --abstr_ref_prep                        false
% 7.78/1.49  --abstr_ref_until_sat                   false
% 7.78/1.49  --abstr_ref_sig_restrict                funpre
% 7.78/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.49  --abstr_ref_under                       []
% 7.78/1.49  
% 7.78/1.49  ------ SAT Options
% 7.78/1.49  
% 7.78/1.49  --sat_mode                              false
% 7.78/1.49  --sat_fm_restart_options                ""
% 7.78/1.49  --sat_gr_def                            false
% 7.78/1.49  --sat_epr_types                         true
% 7.78/1.49  --sat_non_cyclic_types                  false
% 7.78/1.49  --sat_finite_models                     false
% 7.78/1.49  --sat_fm_lemmas                         false
% 7.78/1.49  --sat_fm_prep                           false
% 7.78/1.49  --sat_fm_uc_incr                        true
% 7.78/1.49  --sat_out_model                         small
% 7.78/1.49  --sat_out_clauses                       false
% 7.78/1.49  
% 7.78/1.49  ------ QBF Options
% 7.78/1.49  
% 7.78/1.49  --qbf_mode                              false
% 7.78/1.49  --qbf_elim_univ                         false
% 7.78/1.49  --qbf_dom_inst                          none
% 7.78/1.49  --qbf_dom_pre_inst                      false
% 7.78/1.49  --qbf_sk_in                             false
% 7.78/1.49  --qbf_pred_elim                         true
% 7.78/1.49  --qbf_split                             512
% 7.78/1.49  
% 7.78/1.49  ------ BMC1 Options
% 7.78/1.49  
% 7.78/1.49  --bmc1_incremental                      false
% 7.78/1.49  --bmc1_axioms                           reachable_all
% 7.78/1.49  --bmc1_min_bound                        0
% 7.78/1.49  --bmc1_max_bound                        -1
% 7.78/1.49  --bmc1_max_bound_default                -1
% 7.78/1.49  --bmc1_symbol_reachability              true
% 7.78/1.49  --bmc1_property_lemmas                  false
% 7.78/1.49  --bmc1_k_induction                      false
% 7.78/1.49  --bmc1_non_equiv_states                 false
% 7.78/1.49  --bmc1_deadlock                         false
% 7.78/1.49  --bmc1_ucm                              false
% 7.78/1.49  --bmc1_add_unsat_core                   none
% 7.78/1.49  --bmc1_unsat_core_children              false
% 7.78/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.49  --bmc1_out_stat                         full
% 7.78/1.49  --bmc1_ground_init                      false
% 7.78/1.49  --bmc1_pre_inst_next_state              false
% 7.78/1.49  --bmc1_pre_inst_state                   false
% 7.78/1.49  --bmc1_pre_inst_reach_state             false
% 7.78/1.49  --bmc1_out_unsat_core                   false
% 7.78/1.49  --bmc1_aig_witness_out                  false
% 7.78/1.49  --bmc1_verbose                          false
% 7.78/1.49  --bmc1_dump_clauses_tptp                false
% 7.78/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.49  --bmc1_dump_file                        -
% 7.78/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.49  --bmc1_ucm_extend_mode                  1
% 7.78/1.49  --bmc1_ucm_init_mode                    2
% 7.78/1.49  --bmc1_ucm_cone_mode                    none
% 7.78/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.49  --bmc1_ucm_relax_model                  4
% 7.78/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.49  --bmc1_ucm_layered_model                none
% 7.78/1.49  --bmc1_ucm_max_lemma_size               10
% 7.78/1.49  
% 7.78/1.49  ------ AIG Options
% 7.78/1.49  
% 7.78/1.49  --aig_mode                              false
% 7.78/1.49  
% 7.78/1.49  ------ Instantiation Options
% 7.78/1.49  
% 7.78/1.49  --instantiation_flag                    true
% 7.78/1.49  --inst_sos_flag                         true
% 7.78/1.49  --inst_sos_phase                        true
% 7.78/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.49  --inst_lit_sel_side                     none
% 7.78/1.49  --inst_solver_per_active                1400
% 7.78/1.49  --inst_solver_calls_frac                1.
% 7.78/1.49  --inst_passive_queue_type               priority_queues
% 7.78/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.49  --inst_passive_queues_freq              [25;2]
% 7.78/1.49  --inst_dismatching                      true
% 7.78/1.49  --inst_eager_unprocessed_to_passive     true
% 7.78/1.49  --inst_prop_sim_given                   true
% 7.78/1.49  --inst_prop_sim_new                     false
% 7.78/1.49  --inst_subs_new                         false
% 7.78/1.49  --inst_eq_res_simp                      false
% 7.78/1.49  --inst_subs_given                       false
% 7.78/1.49  --inst_orphan_elimination               true
% 7.78/1.49  --inst_learning_loop_flag               true
% 7.78/1.49  --inst_learning_start                   3000
% 7.78/1.49  --inst_learning_factor                  2
% 7.78/1.49  --inst_start_prop_sim_after_learn       3
% 7.78/1.49  --inst_sel_renew                        solver
% 7.78/1.49  --inst_lit_activity_flag                true
% 7.78/1.49  --inst_restr_to_given                   false
% 7.78/1.49  --inst_activity_threshold               500
% 7.78/1.49  --inst_out_proof                        true
% 7.78/1.49  
% 7.78/1.49  ------ Resolution Options
% 7.78/1.49  
% 7.78/1.49  --resolution_flag                       false
% 7.78/1.49  --res_lit_sel                           adaptive
% 7.78/1.49  --res_lit_sel_side                      none
% 7.78/1.49  --res_ordering                          kbo
% 7.78/1.49  --res_to_prop_solver                    active
% 7.78/1.49  --res_prop_simpl_new                    false
% 7.78/1.49  --res_prop_simpl_given                  true
% 7.78/1.49  --res_passive_queue_type                priority_queues
% 7.78/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.49  --res_passive_queues_freq               [15;5]
% 7.78/1.49  --res_forward_subs                      full
% 7.78/1.49  --res_backward_subs                     full
% 7.78/1.49  --res_forward_subs_resolution           true
% 7.78/1.49  --res_backward_subs_resolution          true
% 7.78/1.49  --res_orphan_elimination                true
% 7.78/1.49  --res_time_limit                        2.
% 7.78/1.49  --res_out_proof                         true
% 7.78/1.49  
% 7.78/1.49  ------ Superposition Options
% 7.78/1.49  
% 7.78/1.49  --superposition_flag                    true
% 7.78/1.49  --sup_passive_queue_type                priority_queues
% 7.78/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.49  --demod_completeness_check              fast
% 7.78/1.49  --demod_use_ground                      true
% 7.78/1.49  --sup_to_prop_solver                    passive
% 7.78/1.49  --sup_prop_simpl_new                    true
% 7.78/1.49  --sup_prop_simpl_given                  true
% 7.78/1.49  --sup_fun_splitting                     true
% 7.78/1.49  --sup_smt_interval                      50000
% 7.78/1.49  
% 7.78/1.49  ------ Superposition Simplification Setup
% 7.78/1.49  
% 7.78/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.49  --sup_immed_triv                        [TrivRules]
% 7.78/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_immed_bw_main                     []
% 7.78/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.49  --sup_input_bw                          []
% 7.78/1.49  
% 7.78/1.49  ------ Combination Options
% 7.78/1.49  
% 7.78/1.49  --comb_res_mult                         3
% 7.78/1.49  --comb_sup_mult                         2
% 7.78/1.49  --comb_inst_mult                        10
% 7.78/1.49  
% 7.78/1.49  ------ Debug Options
% 7.78/1.49  
% 7.78/1.49  --dbg_backtrace                         false
% 7.78/1.49  --dbg_dump_prop_clauses                 false
% 7.78/1.49  --dbg_dump_prop_clauses_file            -
% 7.78/1.49  --dbg_out_stat                          false
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  ------ Proving...
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  % SZS status Theorem for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  fof(f11,axiom,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f32,plain,(
% 7.78/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f11])).
% 7.78/1.49  
% 7.78/1.49  fof(f66,plain,(
% 7.78/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f32])).
% 7.78/1.49  
% 7.78/1.49  fof(f15,conjecture,(
% 7.78/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f16,negated_conjecture,(
% 7.78/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.78/1.49    inference(negated_conjecture,[],[f15])).
% 7.78/1.49  
% 7.78/1.49  fof(f38,plain,(
% 7.78/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.78/1.49    inference(ennf_transformation,[],[f16])).
% 7.78/1.49  
% 7.78/1.49  fof(f39,plain,(
% 7.78/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.78/1.49    inference(flattening,[],[f38])).
% 7.78/1.49  
% 7.78/1.49  fof(f50,plain,(
% 7.78/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f49,plain,(
% 7.78/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f48,plain,(
% 7.78/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f47,plain,(
% 7.78/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f46,plain,(
% 7.78/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f45,plain,(
% 7.78/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f44,plain,(
% 7.78/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.78/1.49    introduced(choice_axiom,[])).
% 7.78/1.49  
% 7.78/1.49  fof(f51,plain,(
% 7.78/1.49    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.78/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f39,f50,f49,f48,f47,f46,f45,f44])).
% 7.78/1.49  
% 7.78/1.49  fof(f78,plain,(
% 7.78/1.49    m1_pre_topc(sK2,sK0)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f4,axiom,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f22,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f4])).
% 7.78/1.49  
% 7.78/1.49  fof(f55,plain,(
% 7.78/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f22])).
% 7.78/1.49  
% 7.78/1.49  fof(f73,plain,(
% 7.78/1.49    l1_pre_topc(sK0)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f3,axiom,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f21,plain,(
% 7.78/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f3])).
% 7.78/1.49  
% 7.78/1.49  fof(f54,plain,(
% 7.78/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f21])).
% 7.78/1.49  
% 7.78/1.49  fof(f2,axiom,(
% 7.78/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f20,plain,(
% 7.78/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f2])).
% 7.78/1.49  
% 7.78/1.49  fof(f53,plain,(
% 7.78/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f20])).
% 7.78/1.49  
% 7.78/1.49  fof(f5,axiom,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f23,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f5])).
% 7.78/1.49  
% 7.78/1.49  fof(f40,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(nnf_transformation,[],[f23])).
% 7.78/1.49  
% 7.78/1.49  fof(f56,plain,(
% 7.78/1.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f40])).
% 7.78/1.49  
% 7.78/1.49  fof(f84,plain,(
% 7.78/1.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f7,axiom,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f17,plain,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 7.78/1.49    inference(pure_predicate_removal,[],[f7])).
% 7.78/1.49  
% 7.78/1.49  fof(f26,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f17])).
% 7.78/1.49  
% 7.78/1.49  fof(f59,plain,(
% 7.78/1.49    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f26])).
% 7.78/1.49  
% 7.78/1.49  fof(f12,axiom,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f33,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f12])).
% 7.78/1.49  
% 7.78/1.49  fof(f67,plain,(
% 7.78/1.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f33])).
% 7.78/1.49  
% 7.78/1.49  fof(f9,axiom,(
% 7.78/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f29,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.78/1.49    inference(ennf_transformation,[],[f9])).
% 7.78/1.49  
% 7.78/1.49  fof(f30,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.78/1.49    inference(flattening,[],[f29])).
% 7.78/1.49  
% 7.78/1.49  fof(f63,plain,(
% 7.78/1.49    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f30])).
% 7.78/1.49  
% 7.78/1.49  fof(f13,axiom,(
% 7.78/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f34,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.78/1.49    inference(ennf_transformation,[],[f13])).
% 7.78/1.49  
% 7.78/1.49  fof(f35,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.78/1.49    inference(flattening,[],[f34])).
% 7.78/1.49  
% 7.78/1.49  fof(f68,plain,(
% 7.78/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f35])).
% 7.78/1.49  
% 7.78/1.49  fof(f72,plain,(
% 7.78/1.49    v2_pre_topc(sK0)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f77,plain,(
% 7.78/1.49    ~v2_struct_0(sK2)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f79,plain,(
% 7.78/1.49    ~v2_struct_0(sK3)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f1,axiom,(
% 7.78/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f18,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.78/1.49    inference(ennf_transformation,[],[f1])).
% 7.78/1.49  
% 7.78/1.49  fof(f19,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.78/1.49    inference(flattening,[],[f18])).
% 7.78/1.49  
% 7.78/1.49  fof(f52,plain,(
% 7.78/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f19])).
% 7.78/1.49  
% 7.78/1.49  fof(f6,axiom,(
% 7.78/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f24,plain,(
% 7.78/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.78/1.49    inference(ennf_transformation,[],[f6])).
% 7.78/1.49  
% 7.78/1.49  fof(f25,plain,(
% 7.78/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.78/1.49    inference(flattening,[],[f24])).
% 7.78/1.49  
% 7.78/1.49  fof(f58,plain,(
% 7.78/1.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f25])).
% 7.78/1.49  
% 7.78/1.49  fof(f8,axiom,(
% 7.78/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f27,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.78/1.49    inference(ennf_transformation,[],[f8])).
% 7.78/1.49  
% 7.78/1.49  fof(f28,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.78/1.49    inference(flattening,[],[f27])).
% 7.78/1.49  
% 7.78/1.49  fof(f41,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.78/1.49    inference(nnf_transformation,[],[f28])).
% 7.78/1.49  
% 7.78/1.49  fof(f42,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.78/1.49    inference(flattening,[],[f41])).
% 7.78/1.49  
% 7.78/1.49  fof(f61,plain,(
% 7.78/1.49    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f42])).
% 7.78/1.49  
% 7.78/1.49  fof(f91,plain,(
% 7.78/1.49    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.78/1.49    inference(equality_resolution,[],[f61])).
% 7.78/1.49  
% 7.78/1.49  fof(f10,axiom,(
% 7.78/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f31,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.78/1.49    inference(ennf_transformation,[],[f10])).
% 7.78/1.49  
% 7.78/1.49  fof(f65,plain,(
% 7.78/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f31])).
% 7.78/1.49  
% 7.78/1.49  fof(f88,plain,(
% 7.78/1.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f87,plain,(
% 7.78/1.49    sK5 = sK6),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f14,axiom,(
% 7.78/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 7.78/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.49  
% 7.78/1.49  fof(f36,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.78/1.49    inference(ennf_transformation,[],[f14])).
% 7.78/1.49  
% 7.78/1.49  fof(f37,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.78/1.49    inference(flattening,[],[f36])).
% 7.78/1.49  
% 7.78/1.49  fof(f43,plain,(
% 7.78/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.78/1.49    inference(nnf_transformation,[],[f37])).
% 7.78/1.49  
% 7.78/1.49  fof(f70,plain,(
% 7.78/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.78/1.49    inference(cnf_transformation,[],[f43])).
% 7.78/1.49  
% 7.78/1.49  fof(f93,plain,(
% 7.78/1.49    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.78/1.49    inference(equality_resolution,[],[f70])).
% 7.78/1.49  
% 7.78/1.49  fof(f82,plain,(
% 7.78/1.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f81,plain,(
% 7.78/1.49    v1_funct_1(sK4)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f74,plain,(
% 7.78/1.49    ~v2_struct_0(sK1)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f75,plain,(
% 7.78/1.49    v2_pre_topc(sK1)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f76,plain,(
% 7.78/1.49    l1_pre_topc(sK1)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f83,plain,(
% 7.78/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f71,plain,(
% 7.78/1.49    ~v2_struct_0(sK0)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f80,plain,(
% 7.78/1.49    m1_pre_topc(sK3,sK0)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f85,plain,(
% 7.78/1.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f89,plain,(
% 7.78/1.49    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  fof(f86,plain,(
% 7.78/1.49    m1_subset_1(sK6,u1_struct_0(sK2))),
% 7.78/1.49    inference(cnf_transformation,[],[f51])).
% 7.78/1.49  
% 7.78/1.49  cnf(c_14,plain,
% 7.78/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_816,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1326,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 7.78/1.49      | l1_pre_topc(X0_54) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_30,negated_conjecture,
% 7.78/1.49      ( m1_pre_topc(sK2,sK0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_805,negated_conjecture,
% 7.78/1.49      ( m1_pre_topc(sK2,sK0) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_30]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1335,plain,
% 7.78/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_820,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.78/1.49      | ~ l1_pre_topc(X1_54)
% 7.78/1.49      | l1_pre_topc(X0_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1322,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.78/1.49      | l1_pre_topc(X0_54) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1984,plain,
% 7.78/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1335,c_1322]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_35,negated_conjecture,
% 7.78/1.49      ( l1_pre_topc(sK0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_40,plain,
% 7.78/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2277,plain,
% 7.78/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_1984,c_40]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2,plain,
% 7.78/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1,plain,
% 7.78/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_383,plain,
% 7.78/1.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.78/1.49      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_796,plain,
% 7.78/1.49      ( ~ l1_pre_topc(X0_54) | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_383]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1344,plain,
% 7.78/1.49      ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
% 7.78/1.49      | l1_pre_topc(X0_54) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2721,plain,
% 7.78/1.49      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2277,c_1344]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_5,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.78/1.49      | ~ l1_pre_topc(X0)
% 7.78/1.49      | ~ l1_pre_topc(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_212,plain,
% 7.78/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1) ),
% 7.78/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5,c_3]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_213,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.78/1.49      | ~ l1_pre_topc(X1) ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_212]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_797,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.78/1.49      | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
% 7.78/1.49      | ~ l1_pre_topc(X1_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_213]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1343,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) = iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3312,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK2) != iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2721,c_1343]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_24,negated_conjecture,
% 7.78/1.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.78/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_809,negated_conjecture,
% 7.78/1.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_24]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3295,plain,
% 7.78/1.49      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_2721,c_809]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3321,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK3) = iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.78/1.49      inference(light_normalisation,[status(thm)],[c_3312,c_3295]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3567,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,sK3) = iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_3321,c_40,c_1984]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3568,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK3) = iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_3567]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3573,plain,
% 7.78/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1326,c_3568]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3586,plain,
% 7.78/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_3573,c_40,c_1984]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_7,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.78/1.49      | ~ l1_pre_topc(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_818,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.78/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
% 7.78/1.49      | ~ l1_pre_topc(X1_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1324,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) = iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2166,plain,
% 7.78/1.49      ( m1_pre_topc(sK2,X0_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(sK3,X0_54) = iProver_top
% 7.78/1.49      | l1_pre_topc(X0_54) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_809,c_1324]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2180,plain,
% 7.78/1.49      ( m1_pre_topc(sK3,sK2) = iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1326,c_2166]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2393,plain,
% 7.78/1.49      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_2180,c_40,c_1984]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_15,plain,
% 7.78/1.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_12,plain,
% 7.78/1.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.78/1.49      | ~ v1_tsep_1(X0,X2)
% 7.78/1.49      | v1_tsep_1(X0,X1)
% 7.78/1.49      | ~ m1_pre_topc(X0,X2)
% 7.78/1.49      | ~ m1_pre_topc(X1,X2)
% 7.78/1.49      | v2_struct_0(X2)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | ~ l1_pre_topc(X2)
% 7.78/1.49      | ~ v2_pre_topc(X2) ),
% 7.78/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_425,plain,
% 7.78/1.49      ( ~ v1_tsep_1(X0,X1)
% 7.78/1.49      | v1_tsep_1(X0,X2)
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ m1_pre_topc(X2,X1)
% 7.78/1.49      | ~ m1_pre_topc(X0,X2)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X2)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ l1_pre_topc(X2)
% 7.78/1.49      | ~ v2_pre_topc(X1) ),
% 7.78/1.49      inference(resolution,[status(thm)],[c_15,c_12]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ m1_pre_topc(X2,X0)
% 7.78/1.49      | m1_pre_topc(X2,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_447,plain,
% 7.78/1.49      ( ~ v1_tsep_1(X0,X1)
% 7.78/1.49      | v1_tsep_1(X0,X2)
% 7.78/1.49      | ~ m1_pre_topc(X2,X1)
% 7.78/1.49      | ~ m1_pre_topc(X0,X2)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X2)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X1) ),
% 7.78/1.49      inference(forward_subsumption_resolution,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_425,c_3,c_16]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_794,plain,
% 7.78/1.49      ( ~ v1_tsep_1(X0_54,X1_54)
% 7.78/1.49      | v1_tsep_1(X0_54,X2_54)
% 7.78/1.49      | ~ m1_pre_topc(X2_54,X1_54)
% 7.78/1.49      | ~ m1_pre_topc(X0_54,X2_54)
% 7.78/1.49      | v2_struct_0(X1_54)
% 7.78/1.49      | v2_struct_0(X2_54)
% 7.78/1.49      | ~ l1_pre_topc(X1_54)
% 7.78/1.49      | ~ v2_pre_topc(X1_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_447]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1346,plain,
% 7.78/1.49      ( v1_tsep_1(X0_54,X1_54) != iProver_top
% 7.78/1.49      | v1_tsep_1(X0_54,X2_54) = iProver_top
% 7.78/1.49      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X2_54) = iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X1_54) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_4667,plain,
% 7.78/1.49      ( v1_tsep_1(X0_54,sK2) != iProver_top
% 7.78/1.49      | v1_tsep_1(X0_54,sK3) = iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.78/1.49      | v2_struct_0(sK2) = iProver_top
% 7.78/1.49      | v2_struct_0(sK3) = iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.78/1.49      | v2_pre_topc(sK2) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2393,c_1346]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_36,negated_conjecture,
% 7.78/1.49      ( v2_pre_topc(sK0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_39,plain,
% 7.78/1.49      ( v2_pre_topc(sK0) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_31,negated_conjecture,
% 7.78/1.49      ( ~ v2_struct_0(sK2) ),
% 7.78/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_44,plain,
% 7.78/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_29,negated_conjecture,
% 7.78/1.49      ( ~ v2_struct_0(sK3) ),
% 7.78/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_46,plain,
% 7.78/1.49      ( v2_struct_0(sK3) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_0,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | v2_pre_topc(X0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_821,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.78/1.49      | ~ l1_pre_topc(X1_54)
% 7.78/1.49      | ~ v2_pre_topc(X1_54)
% 7.78/1.49      | v2_pre_topc(X0_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1321,plain,
% 7.78/1.49      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X1_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X0_54) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1605,plain,
% 7.78/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.78/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.78/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1335,c_1321]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_15359,plain,
% 7.78/1.49      ( v1_tsep_1(X0_54,sK2) != iProver_top
% 7.78/1.49      | v1_tsep_1(X0_54,sK3) = iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK3) != iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_4667,c_39,c_40,c_44,c_46,c_1605,c_1984]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_15372,plain,
% 7.78/1.49      ( v1_tsep_1(sK2,sK2) != iProver_top
% 7.78/1.49      | v1_tsep_1(sK2,sK3) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_3586,c_15359]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6,plain,
% 7.78/1.49      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.78/1.49      | ~ l1_pre_topc(X0)
% 7.78/1.49      | ~ v2_pre_topc(X0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_9,plain,
% 7.78/1.49      ( v1_tsep_1(X0,X1)
% 7.78/1.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_13,plain,
% 7.78/1.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_203,plain,
% 7.78/1.49      ( v1_tsep_1(X0,X1)
% 7.78/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X1) ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_9,c_13]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_398,plain,
% 7.78/1.49      ( v1_tsep_1(X0,X1)
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X2)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X2)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | X1 != X2
% 7.78/1.49      | u1_struct_0(X0) != k2_struct_0(X2) ),
% 7.78/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_203]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_399,plain,
% 7.78/1.49      ( v1_tsep_1(X0,X1)
% 7.78/1.49      | ~ m1_pre_topc(X0,X1)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 7.78/1.49      inference(unflattening,[status(thm)],[c_398]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_795,plain,
% 7.78/1.49      ( v1_tsep_1(X0_54,X1_54)
% 7.78/1.49      | ~ m1_pre_topc(X0_54,X1_54)
% 7.78/1.49      | ~ l1_pre_topc(X1_54)
% 7.78/1.49      | ~ v2_pre_topc(X1_54)
% 7.78/1.49      | u1_struct_0(X0_54) != k2_struct_0(X1_54) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_399]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_4312,plain,
% 7.78/1.49      ( v1_tsep_1(sK2,X0_54)
% 7.78/1.49      | ~ m1_pre_topc(sK2,X0_54)
% 7.78/1.49      | ~ l1_pre_topc(X0_54)
% 7.78/1.49      | ~ v2_pre_topc(X0_54)
% 7.78/1.49      | u1_struct_0(sK2) != k2_struct_0(X0_54) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_795]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_9458,plain,
% 7.78/1.49      ( v1_tsep_1(sK2,sK2)
% 7.78/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.78/1.49      | ~ l1_pre_topc(sK2)
% 7.78/1.49      | ~ v2_pre_topc(sK2)
% 7.78/1.49      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_4312]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_9459,plain,
% 7.78/1.49      ( u1_struct_0(sK2) != k2_struct_0(sK2)
% 7.78/1.49      | v1_tsep_1(sK2,sK2) = iProver_top
% 7.78/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.78/1.49      | v2_pre_topc(sK2) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_9458]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_20,negated_conjecture,
% 7.78/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.78/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_813,negated_conjecture,
% 7.78/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1329,plain,
% 7.78/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_21,negated_conjecture,
% 7.78/1.49      ( sK5 = sK6 ),
% 7.78/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_812,negated_conjecture,
% 7.78/1.49      ( sK5 = sK6 ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1350,plain,
% 7.78/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 7.78/1.49      inference(light_normalisation,[status(thm)],[c_1329,c_812]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_17,plain,
% 7.78/1.49      ( r1_tmap_1(X0,X1,X2,X3)
% 7.78/1.49      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.78/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.78/1.49      | ~ v1_tsep_1(X4,X0)
% 7.78/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.78/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.78/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.78/1.49      | ~ m1_pre_topc(X4,X5)
% 7.78/1.49      | ~ m1_pre_topc(X4,X0)
% 7.78/1.49      | ~ m1_pre_topc(X0,X5)
% 7.78/1.49      | ~ v1_funct_1(X2)
% 7.78/1.49      | v2_struct_0(X5)
% 7.78/1.49      | v2_struct_0(X4)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X0)
% 7.78/1.49      | ~ l1_pre_topc(X5)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X5)
% 7.78/1.49      | ~ v2_pre_topc(X1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_26,negated_conjecture,
% 7.78/1.49      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_536,plain,
% 7.78/1.49      ( r1_tmap_1(X0,X1,X2,X3)
% 7.78/1.49      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.78/1.49      | ~ v1_tsep_1(X4,X0)
% 7.78/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.78/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.78/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.78/1.49      | ~ m1_pre_topc(X4,X5)
% 7.78/1.49      | ~ m1_pre_topc(X4,X0)
% 7.78/1.49      | ~ m1_pre_topc(X0,X5)
% 7.78/1.49      | ~ v1_funct_1(X2)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X0)
% 7.78/1.49      | v2_struct_0(X5)
% 7.78/1.49      | v2_struct_0(X4)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ l1_pre_topc(X5)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X5)
% 7.78/1.49      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.78/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 7.78/1.49      | sK4 != X2 ),
% 7.78/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_537,plain,
% 7.78/1.49      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.78/1.49      | r1_tmap_1(X3,X1,sK4,X4)
% 7.78/1.49      | ~ v1_tsep_1(X0,X3)
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.78/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.78/1.49      | ~ m1_pre_topc(X0,X2)
% 7.78/1.49      | ~ m1_pre_topc(X0,X3)
% 7.78/1.49      | ~ m1_pre_topc(X3,X2)
% 7.78/1.49      | ~ v1_funct_1(sK4)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X3)
% 7.78/1.49      | v2_struct_0(X2)
% 7.78/1.49      | v2_struct_0(X0)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ l1_pre_topc(X2)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X2)
% 7.78/1.49      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.78/1.49      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.78/1.49      inference(unflattening,[status(thm)],[c_536]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_27,negated_conjecture,
% 7.78/1.49      ( v1_funct_1(sK4) ),
% 7.78/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_541,plain,
% 7.78/1.49      ( ~ m1_pre_topc(X3,X2)
% 7.78/1.49      | ~ m1_pre_topc(X0,X3)
% 7.78/1.49      | ~ m1_pre_topc(X0,X2)
% 7.78/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.78/1.49      | ~ v1_tsep_1(X0,X3)
% 7.78/1.49      | r1_tmap_1(X3,X1,sK4,X4)
% 7.78/1.49      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X3)
% 7.78/1.49      | v2_struct_0(X2)
% 7.78/1.49      | v2_struct_0(X0)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ l1_pre_topc(X2)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X2)
% 7.78/1.49      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.78/1.49      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_537,c_27]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_542,plain,
% 7.78/1.49      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.78/1.49      | r1_tmap_1(X3,X1,sK4,X4)
% 7.78/1.49      | ~ v1_tsep_1(X0,X3)
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.78/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.78/1.49      | ~ m1_pre_topc(X0,X2)
% 7.78/1.49      | ~ m1_pre_topc(X0,X3)
% 7.78/1.49      | ~ m1_pre_topc(X3,X2)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X2)
% 7.78/1.49      | v2_struct_0(X0)
% 7.78/1.49      | v2_struct_0(X3)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ l1_pre_topc(X2)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X2)
% 7.78/1.49      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.78/1.49      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_541]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_585,plain,
% 7.78/1.49      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.78/1.49      | r1_tmap_1(X3,X1,sK4,X4)
% 7.78/1.49      | ~ v1_tsep_1(X0,X3)
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.78/1.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.78/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.78/1.49      | ~ m1_pre_topc(X0,X3)
% 7.78/1.49      | ~ m1_pre_topc(X3,X2)
% 7.78/1.49      | v2_struct_0(X1)
% 7.78/1.49      | v2_struct_0(X2)
% 7.78/1.49      | v2_struct_0(X0)
% 7.78/1.49      | v2_struct_0(X3)
% 7.78/1.49      | ~ l1_pre_topc(X1)
% 7.78/1.49      | ~ l1_pre_topc(X2)
% 7.78/1.49      | ~ v2_pre_topc(X1)
% 7.78/1.49      | ~ v2_pre_topc(X2)
% 7.78/1.49      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.78/1.49      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.78/1.49      inference(forward_subsumption_resolution,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_542,c_16]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_792,plain,
% 7.78/1.49      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
% 7.78/1.49      | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
% 7.78/1.49      | ~ v1_tsep_1(X0_54,X3_54)
% 7.78/1.49      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 7.78/1.49      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 7.78/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 7.78/1.49      | ~ m1_pre_topc(X0_54,X3_54)
% 7.78/1.49      | ~ m1_pre_topc(X3_54,X2_54)
% 7.78/1.49      | v2_struct_0(X1_54)
% 7.78/1.49      | v2_struct_0(X2_54)
% 7.78/1.49      | v2_struct_0(X0_54)
% 7.78/1.49      | v2_struct_0(X3_54)
% 7.78/1.49      | ~ l1_pre_topc(X1_54)
% 7.78/1.49      | ~ l1_pre_topc(X2_54)
% 7.78/1.49      | ~ v2_pre_topc(X1_54)
% 7.78/1.49      | ~ v2_pre_topc(X2_54)
% 7.78/1.49      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 7.78/1.49      | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_585]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1348,plain,
% 7.78/1.49      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 7.78/1.49      | u1_struct_0(X1_54) != u1_struct_0(sK3)
% 7.78/1.49      | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
% 7.78/1.49      | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
% 7.78/1.49      | v1_tsep_1(X2_54,X1_54) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.78/1.49      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 7.78/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X2_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X3_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | l1_pre_topc(X0_54) != iProver_top
% 7.78/1.49      | l1_pre_topc(X3_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X0_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X3_54) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2400,plain,
% 7.78/1.49      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.78/1.49      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.78/1.49      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.78/1.49      | v1_tsep_1(X1_54,X0_54) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X2_54) = iProver_top
% 7.78/1.49      | v2_struct_0(sK1) = iProver_top
% 7.78/1.49      | l1_pre_topc(X2_54) != iProver_top
% 7.78/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.78/1.49      | v2_pre_topc(X2_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.78/1.49      inference(equality_resolution,[status(thm)],[c_1348]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_34,negated_conjecture,
% 7.78/1.49      ( ~ v2_struct_0(sK1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_41,plain,
% 7.78/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_33,negated_conjecture,
% 7.78/1.49      ( v2_pre_topc(sK1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_42,plain,
% 7.78/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_32,negated_conjecture,
% 7.78/1.49      ( l1_pre_topc(sK1) ),
% 7.78/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_43,plain,
% 7.78/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2462,plain,
% 7.78/1.49      ( v2_pre_topc(X2_54) != iProver_top
% 7.78/1.49      | v2_struct_0(X2_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.78/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.78/1.49      | v1_tsep_1(X1_54,X0_54) != iProver_top
% 7.78/1.49      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.78/1.49      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.78/1.49      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.78/1.49      | l1_pre_topc(X2_54) != iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_2400,c_41,c_42,c_43]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2463,plain,
% 7.78/1.49      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.78/1.49      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.78/1.49      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.78/1.49      | v1_tsep_1(X1_54,X0_54) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X2_54) = iProver_top
% 7.78/1.49      | l1_pre_topc(X2_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X2_54) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_2462]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2466,plain,
% 7.78/1.49      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.78/1.49      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.78/1.49      | v1_tsep_1(X0_54,sK3) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.78/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.78/1.49      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.78/1.49      | v2_struct_0(sK3) = iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X1_54) != iProver_top ),
% 7.78/1.49      inference(equality_resolution,[status(thm)],[c_2463]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_25,negated_conjecture,
% 7.78/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.78/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_50,plain,
% 7.78/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2544,plain,
% 7.78/1.49      ( v2_struct_0(X0_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.78/1.49      | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.78/1.49      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.78/1.49      | v1_tsep_1(X0_54,sK3) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X1_54) != iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_2466,c_46,c_50]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2545,plain,
% 7.78/1.49      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.78/1.49      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.78/1.49      | v1_tsep_1(X0_54,sK3) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.78/1.49      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.78/1.49      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.78/1.49      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.78/1.49      | v2_struct_0(X1_54) = iProver_top
% 7.78/1.49      | v2_struct_0(X0_54) = iProver_top
% 7.78/1.49      | l1_pre_topc(X1_54) != iProver_top
% 7.78/1.49      | v2_pre_topc(X1_54) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_2544]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2550,plain,
% 7.78/1.49      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 7.78/1.49      | v1_tsep_1(sK2,sK3) != iProver_top
% 7.78/1.49      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.78/1.49      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 7.78/1.49      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.78/1.49      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.78/1.49      | v2_struct_0(sK0) = iProver_top
% 7.78/1.49      | v2_struct_0(sK2) = iProver_top
% 7.78/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.78/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1350,c_2545]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_37,negated_conjecture,
% 7.78/1.49      ( ~ v2_struct_0(sK0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_38,plain,
% 7.78/1.49      ( v2_struct_0(sK0) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_28,negated_conjecture,
% 7.78/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.78/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_47,plain,
% 7.78/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_23,negated_conjecture,
% 7.78/1.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_51,plain,
% 7.78/1.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_19,negated_conjecture,
% 7.78/1.49      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 7.78/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_54,plain,
% 7.78/1.49      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_22,negated_conjecture,
% 7.78/1.49      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_811,negated_conjecture,
% 7.78/1.49      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.78/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1330,plain,
% 7.78/1.49      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1349,plain,
% 7.78/1.49      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.78/1.49      inference(light_normalisation,[status(thm)],[c_1330,c_812]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3039,plain,
% 7.78/1.49      ( m1_pre_topc(sK2,sK3) != iProver_top
% 7.78/1.49      | v1_tsep_1(sK2,sK3) != iProver_top ),
% 7.78/1.49      inference(global_propositional_subsumption,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_2550,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1349]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3040,plain,
% 7.78/1.49      ( v1_tsep_1(sK2,sK3) != iProver_top
% 7.78/1.49      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 7.78/1.49      inference(renaming,[status(thm)],[c_3039]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2599,plain,
% 7.78/1.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_816]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2600,plain,
% 7.78/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.78/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_2599]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(contradiction,plain,
% 7.78/1.49      ( $false ),
% 7.78/1.49      inference(minisat,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_15372,c_9459,c_3573,c_3040,c_2721,c_2600,c_1984,
% 7.78/1.49                 c_1605,c_40,c_39]) ).
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  ------                               Statistics
% 7.78/1.49  
% 7.78/1.49  ------ General
% 7.78/1.49  
% 7.78/1.49  abstr_ref_over_cycles:                  0
% 7.78/1.49  abstr_ref_under_cycles:                 0
% 7.78/1.49  gc_basic_clause_elim:                   0
% 7.78/1.49  forced_gc_time:                         0
% 7.78/1.49  parsing_time:                           0.009
% 7.78/1.49  unif_index_cands_time:                  0.
% 7.78/1.49  unif_index_add_time:                    0.
% 7.78/1.49  orderings_time:                         0.
% 7.78/1.49  out_proof_time:                         0.014
% 7.78/1.49  total_time:                             0.58
% 7.78/1.49  num_of_symbols:                         60
% 7.78/1.49  num_of_terms:                           6203
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing
% 7.78/1.49  
% 7.78/1.49  num_of_splits:                          0
% 7.78/1.49  num_of_split_atoms:                     0
% 7.78/1.49  num_of_reused_defs:                     0
% 7.78/1.49  num_eq_ax_congr_red:                    11
% 7.78/1.49  num_of_sem_filtered_clauses:            1
% 7.78/1.49  num_of_subtypes:                        3
% 7.78/1.49  monotx_restored_types:                  0
% 7.78/1.49  sat_num_of_epr_types:                   0
% 7.78/1.49  sat_num_of_non_cyclic_types:            0
% 7.78/1.49  sat_guarded_non_collapsed_types:        0
% 7.78/1.49  num_pure_diseq_elim:                    0
% 7.78/1.49  simp_replaced_by:                       0
% 7.78/1.49  res_preprocessed:                       162
% 7.78/1.49  prep_upred:                             0
% 7.78/1.49  prep_unflattend:                        3
% 7.78/1.49  smt_new_axioms:                         0
% 7.78/1.49  pred_elim_cands:                        7
% 7.78/1.49  pred_elim:                              5
% 7.78/1.49  pred_elim_cl:                           7
% 7.78/1.49  pred_elim_cycles:                       7
% 7.78/1.49  merged_defs:                            0
% 7.78/1.49  merged_defs_ncl:                        0
% 7.78/1.49  bin_hyper_res:                          0
% 7.78/1.49  prep_cycles:                            4
% 7.78/1.49  pred_elim_time:                         0.009
% 7.78/1.49  splitting_time:                         0.
% 7.78/1.49  sem_filter_time:                        0.
% 7.78/1.49  monotx_time:                            0.
% 7.78/1.49  subtype_inf_time:                       0.
% 7.78/1.49  
% 7.78/1.49  ------ Problem properties
% 7.78/1.49  
% 7.78/1.49  clauses:                                30
% 7.78/1.49  conjectures:                            17
% 7.78/1.49  epr:                                    17
% 7.78/1.49  horn:                                   27
% 7.78/1.49  ground:                                 17
% 7.78/1.49  unary:                                  17
% 7.78/1.49  binary:                                 2
% 7.78/1.49  lits:                                   95
% 7.78/1.49  lits_eq:                                8
% 7.78/1.49  fd_pure:                                0
% 7.78/1.49  fd_pseudo:                              0
% 7.78/1.49  fd_cond:                                0
% 7.78/1.49  fd_pseudo_cond:                         0
% 7.78/1.49  ac_symbols:                             0
% 7.78/1.49  
% 7.78/1.49  ------ Propositional Solver
% 7.78/1.49  
% 7.78/1.49  prop_solver_calls:                      33
% 7.78/1.49  prop_fast_solver_calls:                 2116
% 7.78/1.49  smt_solver_calls:                       0
% 7.78/1.49  smt_fast_solver_calls:                  0
% 7.78/1.49  prop_num_of_clauses:                    6476
% 7.78/1.49  prop_preprocess_simplified:             9669
% 7.78/1.49  prop_fo_subsumed:                       157
% 7.78/1.49  prop_solver_time:                       0.
% 7.78/1.49  smt_solver_time:                        0.
% 7.78/1.49  smt_fast_solver_time:                   0.
% 7.78/1.49  prop_fast_solver_time:                  0.
% 7.78/1.49  prop_unsat_core_time:                   0.001
% 7.78/1.49  
% 7.78/1.49  ------ QBF
% 7.78/1.49  
% 7.78/1.49  qbf_q_res:                              0
% 7.78/1.49  qbf_num_tautologies:                    0
% 7.78/1.49  qbf_prep_cycles:                        0
% 7.78/1.49  
% 7.78/1.49  ------ BMC1
% 7.78/1.49  
% 7.78/1.49  bmc1_current_bound:                     -1
% 7.78/1.49  bmc1_last_solved_bound:                 -1
% 7.78/1.49  bmc1_unsat_core_size:                   -1
% 7.78/1.49  bmc1_unsat_core_parents_size:           -1
% 7.78/1.49  bmc1_merge_next_fun:                    0
% 7.78/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.78/1.49  
% 7.78/1.49  ------ Instantiation
% 7.78/1.49  
% 7.78/1.49  inst_num_of_clauses:                    1397
% 7.78/1.49  inst_num_in_passive:                    139
% 7.78/1.49  inst_num_in_active:                     911
% 7.78/1.49  inst_num_in_unprocessed:                347
% 7.78/1.49  inst_num_of_loops:                      1000
% 7.78/1.49  inst_num_of_learning_restarts:          0
% 7.78/1.49  inst_num_moves_active_passive:          81
% 7.78/1.49  inst_lit_activity:                      0
% 7.78/1.49  inst_lit_activity_moves:                0
% 7.78/1.49  inst_num_tautologies:                   0
% 7.78/1.49  inst_num_prop_implied:                  0
% 7.78/1.49  inst_num_existing_simplified:           0
% 7.78/1.49  inst_num_eq_res_simplified:             0
% 7.78/1.49  inst_num_child_elim:                    0
% 7.78/1.49  inst_num_of_dismatching_blockings:      880
% 7.78/1.49  inst_num_of_non_proper_insts:           2873
% 7.78/1.49  inst_num_of_duplicates:                 0
% 7.78/1.49  inst_inst_num_from_inst_to_res:         0
% 7.78/1.49  inst_dismatching_checking_time:         0.
% 7.78/1.49  
% 7.78/1.49  ------ Resolution
% 7.78/1.49  
% 7.78/1.49  res_num_of_clauses:                     0
% 7.78/1.49  res_num_in_passive:                     0
% 7.78/1.49  res_num_in_active:                      0
% 7.78/1.49  res_num_of_loops:                       166
% 7.78/1.49  res_forward_subset_subsumed:            319
% 7.78/1.49  res_backward_subset_subsumed:           2
% 7.78/1.49  res_forward_subsumed:                   0
% 7.78/1.49  res_backward_subsumed:                  0
% 7.78/1.49  res_forward_subsumption_resolution:     4
% 7.78/1.49  res_backward_subsumption_resolution:    0
% 7.78/1.49  res_clause_to_clause_subsumption:       4276
% 7.78/1.49  res_orphan_elimination:                 0
% 7.78/1.49  res_tautology_del:                      510
% 7.78/1.49  res_num_eq_res_simplified:              0
% 7.78/1.49  res_num_sel_changes:                    0
% 7.78/1.49  res_moves_from_active_to_pass:          0
% 7.78/1.49  
% 7.78/1.49  ------ Superposition
% 7.78/1.49  
% 7.78/1.49  sup_time_total:                         0.
% 7.78/1.49  sup_time_generating:                    0.
% 7.78/1.49  sup_time_sim_full:                      0.
% 7.78/1.49  sup_time_sim_immed:                     0.
% 7.78/1.49  
% 7.78/1.49  sup_num_of_clauses:                     642
% 7.78/1.49  sup_num_in_active:                      186
% 7.78/1.49  sup_num_in_passive:                     456
% 7.78/1.49  sup_num_of_loops:                       199
% 7.78/1.49  sup_fw_superposition:                   769
% 7.78/1.49  sup_bw_superposition:                   644
% 7.78/1.49  sup_immediate_simplified:               781
% 7.78/1.49  sup_given_eliminated:                   0
% 7.78/1.49  comparisons_done:                       0
% 7.78/1.49  comparisons_avoided:                    0
% 7.78/1.49  
% 7.78/1.49  ------ Simplifications
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  sim_fw_subset_subsumed:                 349
% 7.78/1.49  sim_bw_subset_subsumed:                 71
% 7.78/1.49  sim_fw_subsumed:                        170
% 7.78/1.49  sim_bw_subsumed:                        14
% 7.78/1.49  sim_fw_subsumption_res:                 0
% 7.78/1.49  sim_bw_subsumption_res:                 0
% 7.78/1.49  sim_tautology_del:                      24
% 7.78/1.49  sim_eq_tautology_del:                   0
% 7.78/1.49  sim_eq_res_simp:                        0
% 7.78/1.49  sim_fw_demodulated:                     0
% 7.78/1.49  sim_bw_demodulated:                     10
% 7.78/1.49  sim_light_normalised:                   304
% 7.78/1.49  sim_joinable_taut:                      0
% 7.78/1.49  sim_joinable_simp:                      0
% 7.78/1.49  sim_ac_normalised:                      0
% 7.78/1.49  sim_smt_subsumption:                    0
% 7.78/1.49  
%------------------------------------------------------------------------------
