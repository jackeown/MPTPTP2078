%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:28 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 528 expanded)
%              Number of clauses        :  102 ( 121 expanded)
%              Number of leaves         :   27 ( 236 expanded)
%              Depth                    :   18
%              Number of atoms          : 1026 (7331 expanded)
%              Number of equality atoms :  188 (1060 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f53,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f51,f50,f49,f48,f47,f46,f45])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f85,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f56,plain,(
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

fof(f55,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_971,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2365,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_2966,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2365])).

cnf(c_4908,plain,
    ( k2_struct_0(X0) != u1_struct_0(X1)
    | k2_struct_0(X0) = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_7975,plain,
    ( k2_struct_0(X0) != u1_struct_0(X1)
    | k2_struct_0(X0) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_4908])).

cnf(c_9301,plain,
    ( k2_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k2_struct_0(X0) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_7975])).

cnf(c_12340,plain,
    ( k2_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k2_struct_0(sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_9301])).

cnf(c_3837,plain,
    ( k2_struct_0(X0) != u1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_4963,plain,
    ( k2_struct_0(X0) != u1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3837])).

cnf(c_6640,plain,
    ( k2_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4963])).

cnf(c_2780,plain,
    ( X0 != X1
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_3539,plain,
    ( X0 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_5000,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3539])).

cnf(c_6553,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5000])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1927,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4192,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3783,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[status(thm)],[c_12,c_32])).

cnf(c_10,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_16,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_214,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_215,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_445,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k2_struct_0(X2) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_215])).

cnf(c_446,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_541,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_542,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_546,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_29])).

cnf(c_547,plain,
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
    inference(renaming,[status(thm)],[c_546])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_590,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_547,c_18])).

cnf(c_612,plain,
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
    inference(resolution_lifted,[status(thm)],[c_446,c_590])).

cnf(c_613,plain,
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
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_657,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_613,c_4,c_1])).

cnf(c_1890,plain,
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
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_2101,plain,
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
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_3219,plain,
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
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3198,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1589,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_224,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_4])).

cnf(c_225,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_1572,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_2708,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1572])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2130,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

cnf(c_2131,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_2914,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2708,c_42,c_2131])).

cnf(c_2915,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_2914])).

cnf(c_2922,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_2915])).

cnf(c_2923,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2922])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1958,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | X1 = u1_struct_0(X0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2567,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_2752,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2567])).

cnf(c_976,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2552,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_976,c_26])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_408,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_2230,plain,
    ( ~ l1_pre_topc(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_970,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2181,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2128,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_30])).

cnf(c_972,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1911,plain,
    ( X0 != sK3
    | u1_struct_0(X0) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_2090,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_1889,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1586,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1641,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1586,c_23])).

cnf(c_1810,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1641])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1585,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1624,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1585,c_23])).

cnf(c_1802,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1624])).

cnf(c_999,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_985,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12340,c_6640,c_6553,c_4192,c_3783,c_3219,c_3198,c_2923,c_2752,c_2552,c_2230,c_2181,c_2130,c_2128,c_2090,c_1889,c_1810,c_1802,c_999,c_985,c_21,c_25,c_26,c_27,c_30,c_31,c_33,c_34,c_35,c_36,c_37,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.55/1.11  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.11  
% 3.55/1.11  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/1.11  
% 3.55/1.11  ------  iProver source info
% 3.55/1.11  
% 3.55/1.11  git: date: 2020-06-30 10:37:57 +0100
% 3.55/1.11  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/1.11  git: non_committed_changes: false
% 3.55/1.11  git: last_make_outside_of_git: false
% 3.55/1.11  
% 3.55/1.11  ------ 
% 3.55/1.11  ------ Parsing...
% 3.55/1.11  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/1.11  
% 3.55/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.55/1.11  
% 3.55/1.11  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/1.11  
% 3.55/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/1.11  ------ Proving...
% 3.55/1.11  ------ Problem Properties 
% 3.55/1.11  
% 3.55/1.11  
% 3.55/1.11  clauses                                 33
% 3.55/1.11  conjectures                             17
% 3.55/1.11  EPR                                     16
% 3.55/1.11  Horn                                    31
% 3.55/1.11  unary                                   17
% 3.55/1.11  binary                                  3
% 3.55/1.11  lits                                    96
% 3.55/1.11  lits eq                                 14
% 3.55/1.11  fd_pure                                 0
% 3.55/1.11  fd_pseudo                               0
% 3.55/1.11  fd_cond                                 0
% 3.55/1.11  fd_pseudo_cond                          2
% 3.55/1.11  AC symbols                              0
% 3.55/1.11  
% 3.55/1.11  ------ Input Options Time Limit: Unbounded
% 3.55/1.11  
% 3.55/1.11  
% 3.55/1.11  ------ 
% 3.55/1.11  Current options:
% 3.55/1.11  ------ 
% 3.55/1.11  
% 3.55/1.11  
% 3.55/1.11  
% 3.55/1.11  
% 3.55/1.11  ------ Proving...
% 3.55/1.11  
% 3.55/1.11  
% 3.55/1.11  % SZS status Theorem for theBenchmark.p
% 3.55/1.11  
% 3.55/1.11  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/1.11  
% 3.55/1.11  fof(f1,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f18,plain,(
% 3.55/1.11    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f1])).
% 3.55/1.11  
% 3.55/1.11  fof(f19,plain,(
% 3.55/1.11    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(flattening,[],[f18])).
% 3.55/1.11  
% 3.55/1.11  fof(f53,plain,(
% 3.55/1.11    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f19])).
% 3.55/1.11  
% 3.55/1.11  fof(f10,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f30,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f10])).
% 3.55/1.11  
% 3.55/1.11  fof(f64,plain,(
% 3.55/1.11    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f30])).
% 3.55/1.11  
% 3.55/1.11  fof(f16,conjecture,(
% 3.55/1.11    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f17,negated_conjecture,(
% 3.55/1.11    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.55/1.11    inference(negated_conjecture,[],[f16])).
% 3.55/1.11  
% 3.55/1.11  fof(f39,plain,(
% 3.55/1.11    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.55/1.11    inference(ennf_transformation,[],[f17])).
% 3.55/1.11  
% 3.55/1.11  fof(f40,plain,(
% 3.55/1.11    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.55/1.11    inference(flattening,[],[f39])).
% 3.55/1.11  
% 3.55/1.11  fof(f51,plain,(
% 3.55/1.11    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.55/1.11    introduced(choice_axiom,[])).
% 3.55/1.11  
% 3.55/1.11  fof(f50,plain,(
% 3.55/1.11    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.55/1.11    introduced(choice_axiom,[])).
% 3.55/1.11  
% 3.55/1.11  fof(f49,plain,(
% 3.55/1.11    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.55/1.11    introduced(choice_axiom,[])).
% 3.55/1.11  
% 3.55/1.11  fof(f48,plain,(
% 3.55/1.11    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.55/1.11    introduced(choice_axiom,[])).
% 3.55/1.11  
% 3.55/1.11  fof(f47,plain,(
% 3.55/1.11    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.55/1.11    introduced(choice_axiom,[])).
% 3.55/1.11  
% 3.55/1.11  fof(f46,plain,(
% 3.55/1.11    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.55/1.11    introduced(choice_axiom,[])).
% 3.55/1.11  
% 3.55/1.11  fof(f45,plain,(
% 3.55/1.11    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.55/1.11    introduced(choice_axiom,[])).
% 3.55/1.11  
% 3.55/1.11  fof(f52,plain,(
% 3.55/1.11    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.55/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f51,f50,f49,f48,f47,f46,f45])).
% 3.55/1.11  
% 3.55/1.11  fof(f81,plain,(
% 3.55/1.11    m1_pre_topc(sK2,sK0)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f9,axiom,(
% 3.55/1.11    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f28,plain,(
% 3.55/1.11    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.55/1.11    inference(ennf_transformation,[],[f9])).
% 3.55/1.11  
% 3.55/1.11  fof(f29,plain,(
% 3.55/1.11    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.55/1.11    inference(flattening,[],[f28])).
% 3.55/1.11  
% 3.55/1.11  fof(f63,plain,(
% 3.55/1.11    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f29])).
% 3.55/1.11  
% 3.55/1.11  fof(f11,axiom,(
% 3.55/1.11    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f31,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.55/1.11    inference(ennf_transformation,[],[f11])).
% 3.55/1.11  
% 3.55/1.11  fof(f32,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.55/1.11    inference(flattening,[],[f31])).
% 3.55/1.11  
% 3.55/1.11  fof(f42,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.55/1.11    inference(nnf_transformation,[],[f32])).
% 3.55/1.11  
% 3.55/1.11  fof(f43,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.55/1.11    inference(flattening,[],[f42])).
% 3.55/1.11  
% 3.55/1.11  fof(f67,plain,(
% 3.55/1.11    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f43])).
% 3.55/1.11  
% 3.55/1.11  fof(f94,plain,(
% 3.55/1.11    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.55/1.11    inference(equality_resolution,[],[f67])).
% 3.55/1.11  
% 3.55/1.11  fof(f12,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f33,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f12])).
% 3.55/1.11  
% 3.55/1.11  fof(f69,plain,(
% 3.55/1.11    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f33])).
% 3.55/1.11  
% 3.55/1.11  fof(f15,axiom,(
% 3.55/1.11    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f37,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.11    inference(ennf_transformation,[],[f15])).
% 3.55/1.11  
% 3.55/1.11  fof(f38,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.11    inference(flattening,[],[f37])).
% 3.55/1.11  
% 3.55/1.11  fof(f44,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.11    inference(nnf_transformation,[],[f38])).
% 3.55/1.11  
% 3.55/1.11  fof(f73,plain,(
% 3.55/1.11    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f44])).
% 3.55/1.11  
% 3.55/1.11  fof(f96,plain,(
% 3.55/1.11    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.11    inference(equality_resolution,[],[f73])).
% 3.55/1.11  
% 3.55/1.11  fof(f85,plain,(
% 3.55/1.11    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f84,plain,(
% 3.55/1.11    v1_funct_1(sK4)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f14,axiom,(
% 3.55/1.11    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f35,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.55/1.11    inference(ennf_transformation,[],[f14])).
% 3.55/1.11  
% 3.55/1.11  fof(f36,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.55/1.11    inference(flattening,[],[f35])).
% 3.55/1.11  
% 3.55/1.11  fof(f71,plain,(
% 3.55/1.11    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f36])).
% 3.55/1.11  
% 3.55/1.11  fof(f5,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f24,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f5])).
% 3.55/1.11  
% 3.55/1.11  fof(f57,plain,(
% 3.55/1.11    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f24])).
% 3.55/1.11  
% 3.55/1.11  fof(f2,axiom,(
% 3.55/1.11    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f20,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.55/1.11    inference(ennf_transformation,[],[f2])).
% 3.55/1.11  
% 3.55/1.11  fof(f21,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.55/1.11    inference(flattening,[],[f20])).
% 3.55/1.11  
% 3.55/1.11  fof(f54,plain,(
% 3.55/1.11    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f21])).
% 3.55/1.11  
% 3.55/1.11  fof(f6,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f25,plain,(
% 3.55/1.11    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f6])).
% 3.55/1.11  
% 3.55/1.11  fof(f58,plain,(
% 3.55/1.11    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f25])).
% 3.55/1.11  
% 3.55/1.11  fof(f13,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f34,plain,(
% 3.55/1.11    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f13])).
% 3.55/1.11  
% 3.55/1.11  fof(f70,plain,(
% 3.55/1.11    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f34])).
% 3.55/1.11  
% 3.55/1.11  fof(f87,plain,(
% 3.55/1.11    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f8,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f27,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f8])).
% 3.55/1.11  
% 3.55/1.11  fof(f41,plain,(
% 3.55/1.11    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(nnf_transformation,[],[f27])).
% 3.55/1.11  
% 3.55/1.11  fof(f61,plain,(
% 3.55/1.11    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f41])).
% 3.55/1.11  
% 3.55/1.11  fof(f76,plain,(
% 3.55/1.11    l1_pre_topc(sK0)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f7,axiom,(
% 3.55/1.11    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f26,plain,(
% 3.55/1.11    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.55/1.11    inference(ennf_transformation,[],[f7])).
% 3.55/1.11  
% 3.55/1.11  fof(f59,plain,(
% 3.55/1.11    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.55/1.11    inference(cnf_transformation,[],[f26])).
% 3.55/1.11  
% 3.55/1.11  fof(f4,axiom,(
% 3.55/1.11    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f23,plain,(
% 3.55/1.11    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f4])).
% 3.55/1.11  
% 3.55/1.11  fof(f56,plain,(
% 3.55/1.11    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f23])).
% 3.55/1.11  
% 3.55/1.11  fof(f3,axiom,(
% 3.55/1.11    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.55/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.11  
% 3.55/1.11  fof(f22,plain,(
% 3.55/1.11    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.55/1.11    inference(ennf_transformation,[],[f3])).
% 3.55/1.11  
% 3.55/1.11  fof(f55,plain,(
% 3.55/1.11    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.55/1.11    inference(cnf_transformation,[],[f22])).
% 3.55/1.11  
% 3.55/1.11  fof(f83,plain,(
% 3.55/1.11    m1_pre_topc(sK3,sK0)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f91,plain,(
% 3.55/1.11    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f90,plain,(
% 3.55/1.11    sK5 = sK6),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f89,plain,(
% 3.55/1.11    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f92,plain,(
% 3.55/1.11    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f88,plain,(
% 3.55/1.11    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f86,plain,(
% 3.55/1.11    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f82,plain,(
% 3.55/1.11    ~v2_struct_0(sK3)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f80,plain,(
% 3.55/1.11    ~v2_struct_0(sK2)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f79,plain,(
% 3.55/1.11    l1_pre_topc(sK1)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f78,plain,(
% 3.55/1.11    v2_pre_topc(sK1)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f77,plain,(
% 3.55/1.11    ~v2_struct_0(sK1)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f75,plain,(
% 3.55/1.11    v2_pre_topc(sK0)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  fof(f74,plain,(
% 3.55/1.11    ~v2_struct_0(sK0)),
% 3.55/1.11    inference(cnf_transformation,[],[f52])).
% 3.55/1.11  
% 3.55/1.11  cnf(c_971,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_2365,plain,
% 3.55/1.11      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_971]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_2966,plain,
% 3.55/1.11      ( X0 != u1_struct_0(X1)
% 3.55/1.11      | X0 = u1_struct_0(X2)
% 3.55/1.11      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_2365]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_4908,plain,
% 3.55/1.11      ( k2_struct_0(X0) != u1_struct_0(X1)
% 3.55/1.11      | k2_struct_0(X0) = u1_struct_0(X2)
% 3.55/1.11      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_2966]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_7975,plain,
% 3.55/1.11      ( k2_struct_0(X0) != u1_struct_0(X1)
% 3.55/1.11      | k2_struct_0(X0) = u1_struct_0(sK2)
% 3.55/1.11      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_4908]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_9301,plain,
% 3.55/1.11      ( k2_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.11      | k2_struct_0(X0) = u1_struct_0(sK2)
% 3.55/1.11      | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_7975]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_12340,plain,
% 3.55/1.11      ( k2_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.11      | k2_struct_0(sK3) = u1_struct_0(sK2)
% 3.55/1.11      | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_9301]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_3837,plain,
% 3.55/1.11      ( k2_struct_0(X0) != u1_struct_0(X0)
% 3.55/1.11      | k2_struct_0(X0) = u1_struct_0(X1)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(X0) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_2966]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_4963,plain,
% 3.55/1.11      ( k2_struct_0(X0) != u1_struct_0(X0)
% 3.55/1.11      | k2_struct_0(X0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.11      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(X0) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_3837]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_6640,plain,
% 3.55/1.11      ( k2_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.11      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 3.55/1.11      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_4963]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_2780,plain,
% 3.55/1.11      ( X0 != X1 | u1_struct_0(sK2) != X1 | u1_struct_0(sK2) = X0 ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_971]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_3539,plain,
% 3.55/1.11      ( X0 != u1_struct_0(sK2)
% 3.55/1.11      | u1_struct_0(sK2) = X0
% 3.55/1.11      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_2780]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_5000,plain,
% 3.55/1.11      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 3.55/1.11      | u1_struct_0(sK2) = u1_struct_0(X0)
% 3.55/1.11      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_3539]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_6553,plain,
% 3.55/1.11      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK2)
% 3.55/1.11      | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.11      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_5000]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_0,plain,
% 3.55/1.11      ( ~ l1_pre_topc(X0)
% 3.55/1.11      | ~ v1_pre_topc(X0)
% 3.55/1.11      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.55/1.11      inference(cnf_transformation,[],[f53]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_1927,plain,
% 3.55/1.11      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.55/1.11      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.55/1.11      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_0]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_4192,plain,
% 3.55/1.11      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.11      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.11      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.55/1.11      inference(instantiation,[status(thm)],[c_1927]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_12,plain,
% 3.55/1.11      ( ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.55/1.11      inference(cnf_transformation,[],[f64]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_32,negated_conjecture,
% 3.55/1.11      ( m1_pre_topc(sK2,sK0) ),
% 3.55/1.11      inference(cnf_transformation,[],[f81]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_3783,plain,
% 3.55/1.11      ( ~ l1_pre_topc(sK0)
% 3.55/1.11      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.55/1.11      inference(resolution,[status(thm)],[c_12,c_32]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_10,plain,
% 3.55/1.11      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.55/1.11      | ~ v2_pre_topc(X0)
% 3.55/1.11      | ~ l1_pre_topc(X0) ),
% 3.55/1.11      inference(cnf_transformation,[],[f63]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_14,plain,
% 3.55/1.11      ( v1_tsep_1(X0,X1)
% 3.55/1.11      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.55/1.11      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.11      | ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X1) ),
% 3.55/1.11      inference(cnf_transformation,[],[f94]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_16,plain,
% 3.55/1.11      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.11      | ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ l1_pre_topc(X1) ),
% 3.55/1.11      inference(cnf_transformation,[],[f69]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_214,plain,
% 3.55/1.11      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.55/1.11      | v1_tsep_1(X0,X1)
% 3.55/1.11      | ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X1) ),
% 3.55/1.11      inference(global_propositional_subsumption,
% 3.55/1.11                [status(thm)],
% 3.55/1.11                [c_14,c_16]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_215,plain,
% 3.55/1.11      ( v1_tsep_1(X0,X1)
% 3.55/1.11      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.55/1.11      | ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X1) ),
% 3.55/1.11      inference(renaming,[status(thm)],[c_214]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_445,plain,
% 3.55/1.11      ( v1_tsep_1(X0,X1)
% 3.55/1.11      | ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | X1 != X2
% 3.55/1.11      | k2_struct_0(X2) != u1_struct_0(X0) ),
% 3.55/1.11      inference(resolution_lifted,[status(thm)],[c_10,c_215]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_446,plain,
% 3.55/1.11      ( v1_tsep_1(X0,X1)
% 3.55/1.11      | ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | k2_struct_0(X1) != u1_struct_0(X0) ),
% 3.55/1.11      inference(unflattening,[status(thm)],[c_445]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_19,plain,
% 3.55/1.11      ( r1_tmap_1(X0,X1,X2,X3)
% 3.55/1.11      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.55/1.11      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.55/1.11      | ~ v1_tsep_1(X4,X0)
% 3.55/1.11      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.55/1.11      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_pre_topc(X0,X5)
% 3.55/1.11      | ~ m1_pre_topc(X4,X0)
% 3.55/1.11      | ~ m1_pre_topc(X4,X5)
% 3.55/1.11      | v2_struct_0(X5)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X4)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | ~ v1_funct_1(X2)
% 3.55/1.11      | ~ v2_pre_topc(X5)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X5)
% 3.55/1.11      | ~ l1_pre_topc(X1) ),
% 3.55/1.11      inference(cnf_transformation,[],[f96]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_28,negated_conjecture,
% 3.55/1.11      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.55/1.11      inference(cnf_transformation,[],[f85]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_541,plain,
% 3.55/1.11      ( r1_tmap_1(X0,X1,X2,X3)
% 3.55/1.11      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.55/1.11      | ~ v1_tsep_1(X4,X0)
% 3.55/1.11      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.55/1.11      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_pre_topc(X0,X5)
% 3.55/1.11      | ~ m1_pre_topc(X4,X0)
% 3.55/1.11      | ~ m1_pre_topc(X4,X5)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X5)
% 3.55/1.11      | v2_struct_0(X4)
% 3.55/1.11      | ~ v1_funct_1(X2)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ v2_pre_topc(X5)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X5)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.55/1.11      | sK4 != X2 ),
% 3.55/1.11      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_542,plain,
% 3.55/1.11      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.55/1.11      | r1_tmap_1(X3,X1,sK4,X4)
% 3.55/1.11      | ~ v1_tsep_1(X0,X3)
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.55/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_pre_topc(X3,X2)
% 3.55/1.11      | ~ m1_pre_topc(X0,X3)
% 3.55/1.11      | ~ m1_pre_topc(X0,X2)
% 3.55/1.11      | v2_struct_0(X3)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X2)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | ~ v1_funct_1(sK4)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(unflattening,[status(thm)],[c_541]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_29,negated_conjecture,
% 3.55/1.11      ( v1_funct_1(sK4) ),
% 3.55/1.11      inference(cnf_transformation,[],[f84]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_546,plain,
% 3.55/1.11      ( v2_struct_0(X0)
% 3.55/1.11      | v2_struct_0(X2)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X3)
% 3.55/1.11      | ~ m1_pre_topc(X0,X2)
% 3.55/1.11      | ~ m1_pre_topc(X0,X3)
% 3.55/1.11      | ~ m1_pre_topc(X3,X2)
% 3.55/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.55/1.11      | ~ v1_tsep_1(X0,X3)
% 3.55/1.11      | r1_tmap_1(X3,X1,sK4,X4)
% 3.55/1.11      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(global_propositional_subsumption,
% 3.55/1.11                [status(thm)],
% 3.55/1.11                [c_542,c_29]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_547,plain,
% 3.55/1.11      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.55/1.11      | r1_tmap_1(X3,X1,sK4,X4)
% 3.55/1.11      | ~ v1_tsep_1(X0,X3)
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.55/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_pre_topc(X3,X2)
% 3.55/1.11      | ~ m1_pre_topc(X0,X2)
% 3.55/1.11      | ~ m1_pre_topc(X0,X3)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X3)
% 3.55/1.11      | v2_struct_0(X2)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(renaming,[status(thm)],[c_546]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_18,plain,
% 3.55/1.11      ( ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ m1_pre_topc(X2,X0)
% 3.55/1.11      | m1_pre_topc(X2,X1)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X1) ),
% 3.55/1.11      inference(cnf_transformation,[],[f71]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_590,plain,
% 3.55/1.11      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.55/1.11      | r1_tmap_1(X3,X1,sK4,X4)
% 3.55/1.11      | ~ v1_tsep_1(X0,X3)
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.55/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_pre_topc(X3,X2)
% 3.55/1.11      | ~ m1_pre_topc(X0,X3)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X3)
% 3.55/1.11      | v2_struct_0(X2)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(forward_subsumption_resolution,
% 3.55/1.11                [status(thm)],
% 3.55/1.11                [c_547,c_18]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_612,plain,
% 3.55/1.11      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.55/1.11      | r1_tmap_1(X3,X1,sK4,X4)
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.55/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_pre_topc(X5,X6)
% 3.55/1.11      | ~ m1_pre_topc(X0,X3)
% 3.55/1.11      | ~ m1_pre_topc(X3,X2)
% 3.55/1.11      | v2_struct_0(X3)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | v2_struct_0(X2)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | ~ v2_pre_topc(X6)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X6)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | X0 != X5
% 3.55/1.11      | X3 != X6
% 3.55/1.11      | k2_struct_0(X6) != u1_struct_0(X5)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(resolution_lifted,[status(thm)],[c_446,c_590]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_613,plain,
% 3.55/1.11      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.55/1.11      | r1_tmap_1(X3,X1,sK4,X4)
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.55/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_pre_topc(X0,X3)
% 3.55/1.11      | ~ m1_pre_topc(X3,X2)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X2)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | v2_struct_0(X3)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ v2_pre_topc(X3)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X3)
% 3.55/1.11      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(unflattening,[status(thm)],[c_612]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_4,plain,
% 3.55/1.11      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.55/1.11      inference(cnf_transformation,[],[f57]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_1,plain,
% 3.55/1.11      ( ~ m1_pre_topc(X0,X1)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | v2_pre_topc(X0)
% 3.55/1.11      | ~ l1_pre_topc(X1) ),
% 3.55/1.11      inference(cnf_transformation,[],[f54]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_657,plain,
% 3.55/1.11      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.55/1.11      | r1_tmap_1(X3,X1,sK4,X4)
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.55/1.11      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.55/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.55/1.11      | ~ m1_pre_topc(X3,X2)
% 3.55/1.11      | ~ m1_pre_topc(X0,X3)
% 3.55/1.11      | v2_struct_0(X0)
% 3.55/1.11      | v2_struct_0(X1)
% 3.55/1.11      | v2_struct_0(X3)
% 3.55/1.11      | v2_struct_0(X2)
% 3.55/1.11      | ~ v2_pre_topc(X1)
% 3.55/1.11      | ~ v2_pre_topc(X2)
% 3.55/1.11      | ~ l1_pre_topc(X1)
% 3.55/1.11      | ~ l1_pre_topc(X2)
% 3.55/1.11      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.55/1.11      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.11      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.55/1.11      inference(forward_subsumption_resolution,
% 3.55/1.11                [status(thm)],
% 3.55/1.11                [c_613,c_4,c_1]) ).
% 3.55/1.11  
% 3.55/1.11  cnf(c_1890,plain,
% 3.55/1.12      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 3.55/1.12      | r1_tmap_1(sK3,X1,sK4,X3)
% 3.55/1.12      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.55/1.12      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 3.55/1.12      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 3.55/1.12      | ~ m1_pre_topc(X0,sK3)
% 3.55/1.12      | ~ m1_pre_topc(sK3,X2)
% 3.55/1.12      | v2_struct_0(X0)
% 3.55/1.12      | v2_struct_0(X1)
% 3.55/1.12      | v2_struct_0(X2)
% 3.55/1.12      | v2_struct_0(sK3)
% 3.55/1.12      | ~ v2_pre_topc(X1)
% 3.55/1.12      | ~ v2_pre_topc(X2)
% 3.55/1.12      | ~ l1_pre_topc(X1)
% 3.55/1.12      | ~ l1_pre_topc(X2)
% 3.55/1.12      | k2_struct_0(sK3) != u1_struct_0(X0)
% 3.55/1.12      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.12      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_657]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2101,plain,
% 3.55/1.12      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),sK5)
% 3.55/1.12      | r1_tmap_1(sK3,X1,sK4,sK5)
% 3.55/1.12      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 3.55/1.12      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.55/1.12      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 3.55/1.12      | ~ m1_pre_topc(X0,sK3)
% 3.55/1.12      | ~ m1_pre_topc(sK3,X2)
% 3.55/1.12      | v2_struct_0(X0)
% 3.55/1.12      | v2_struct_0(X1)
% 3.55/1.12      | v2_struct_0(X2)
% 3.55/1.12      | v2_struct_0(sK3)
% 3.55/1.12      | ~ v2_pre_topc(X1)
% 3.55/1.12      | ~ v2_pre_topc(X2)
% 3.55/1.12      | ~ l1_pre_topc(X1)
% 3.55/1.12      | ~ l1_pre_topc(X2)
% 3.55/1.12      | k2_struct_0(sK3) != u1_struct_0(X0)
% 3.55/1.12      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.55/1.12      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_1890]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_3219,plain,
% 3.55/1.12      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 3.55/1.12      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.55/1.12      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.55/1.12      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.55/1.12      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.55/1.12      | ~ m1_pre_topc(sK2,sK3)
% 3.55/1.12      | ~ m1_pre_topc(sK3,sK0)
% 3.55/1.12      | v2_struct_0(sK0)
% 3.55/1.12      | v2_struct_0(sK2)
% 3.55/1.12      | v2_struct_0(sK1)
% 3.55/1.12      | v2_struct_0(sK3)
% 3.55/1.12      | ~ v2_pre_topc(sK0)
% 3.55/1.12      | ~ v2_pre_topc(sK1)
% 3.55/1.12      | ~ l1_pre_topc(sK0)
% 3.55/1.12      | ~ l1_pre_topc(sK1)
% 3.55/1.12      | k2_struct_0(sK3) != u1_struct_0(sK2)
% 3.55/1.12      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.55/1.12      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_2101]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_5,plain,
% 3.55/1.12      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.55/1.12      | ~ l1_pre_topc(X0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f58]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_3198,plain,
% 3.55/1.12      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.55/1.12      | ~ l1_pre_topc(sK2) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_5]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_17,plain,
% 3.55/1.12      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f70]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1589,plain,
% 3.55/1.12      ( m1_pre_topc(X0,X0) = iProver_top
% 3.55/1.12      | l1_pre_topc(X0) != iProver_top ),
% 3.55/1.12      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_26,negated_conjecture,
% 3.55/1.12      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.55/1.12      inference(cnf_transformation,[],[f87]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_9,plain,
% 3.55/1.12      ( ~ m1_pre_topc(X0,X1)
% 3.55/1.12      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.55/1.12      | ~ l1_pre_topc(X0)
% 3.55/1.12      | ~ l1_pre_topc(X1) ),
% 3.55/1.12      inference(cnf_transformation,[],[f61]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_224,plain,
% 3.55/1.12      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.55/1.12      | ~ m1_pre_topc(X0,X1)
% 3.55/1.12      | ~ l1_pre_topc(X1) ),
% 3.55/1.12      inference(global_propositional_subsumption,[status(thm)],[c_9,c_4]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_225,plain,
% 3.55/1.12      ( ~ m1_pre_topc(X0,X1)
% 3.55/1.12      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.55/1.12      | ~ l1_pre_topc(X1) ),
% 3.55/1.12      inference(renaming,[status(thm)],[c_224]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1572,plain,
% 3.55/1.12      ( m1_pre_topc(X0,X1) != iProver_top
% 3.55/1.12      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.55/1.12      | l1_pre_topc(X1) != iProver_top ),
% 3.55/1.12      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2708,plain,
% 3.55/1.12      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.55/1.12      | m1_pre_topc(X0,sK3) = iProver_top
% 3.55/1.12      | l1_pre_topc(sK2) != iProver_top ),
% 3.55/1.12      inference(superposition,[status(thm)],[c_26,c_1572]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_37,negated_conjecture,
% 3.55/1.12      ( l1_pre_topc(sK0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f76]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_42,plain,
% 3.55/1.12      ( l1_pre_topc(sK0) = iProver_top ),
% 3.55/1.12      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2130,plain,
% 3.55/1.12      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.55/1.12      inference(resolution,[status(thm)],[c_4,c_32]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2131,plain,
% 3.55/1.12      ( l1_pre_topc(sK0) != iProver_top
% 3.55/1.12      | l1_pre_topc(sK2) = iProver_top ),
% 3.55/1.12      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2914,plain,
% 3.55/1.12      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.55/1.12      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.55/1.12      inference(global_propositional_subsumption,
% 3.55/1.12                [status(thm)],
% 3.55/1.12                [c_2708,c_42,c_2131]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2915,plain,
% 3.55/1.12      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.55/1.12      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.55/1.12      inference(renaming,[status(thm)],[c_2914]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2922,plain,
% 3.55/1.12      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.55/1.12      | l1_pre_topc(sK2) != iProver_top ),
% 3.55/1.12      inference(superposition,[status(thm)],[c_1589,c_2915]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2923,plain,
% 3.55/1.12      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 3.55/1.12      inference(predicate_to_equality_rev,[status(thm)],[c_2922]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_7,plain,
% 3.55/1.12      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.55/1.12      | X2 = X1
% 3.55/1.12      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f59]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1958,plain,
% 3.55/1.12      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.55/1.12      | X1 = u1_struct_0(X0)
% 3.55/1.12      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_7]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2567,plain,
% 3.55/1.12      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.55/1.12      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.55/1.12      | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_1958]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2752,plain,
% 3.55/1.12      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.55/1.12      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.55/1.12      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_2567]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_976,plain,
% 3.55/1.12      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 3.55/1.12      theory(equality) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2552,plain,
% 3.55/1.12      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.55/1.12      | ~ l1_pre_topc(sK3) ),
% 3.55/1.12      inference(resolution,[status(thm)],[c_976,c_26]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_3,plain,
% 3.55/1.12      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f56]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2,plain,
% 3.55/1.12      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f55]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_408,plain,
% 3.55/1.12      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.55/1.12      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2230,plain,
% 3.55/1.12      ( ~ l1_pre_topc(sK3) | k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_408]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_970,plain,( X0 = X0 ),theory(equality) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2181,plain,
% 3.55/1.12      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_970]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_30,negated_conjecture,
% 3.55/1.12      ( m1_pre_topc(sK3,sK0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f83]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2128,plain,
% 3.55/1.12      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.55/1.12      inference(resolution,[status(thm)],[c_4,c_30]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_972,plain,
% 3.55/1.12      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.55/1.12      theory(equality) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1911,plain,
% 3.55/1.12      ( X0 != sK3 | u1_struct_0(X0) = u1_struct_0(sK3) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_972]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_2090,plain,
% 3.55/1.12      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 3.55/1.12      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_1911]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1889,plain,
% 3.55/1.12      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_970]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_22,negated_conjecture,
% 3.55/1.12      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.55/1.12      inference(cnf_transformation,[],[f91]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1586,plain,
% 3.55/1.12      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.55/1.12      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_23,negated_conjecture,
% 3.55/1.12      ( sK5 = sK6 ),
% 3.55/1.12      inference(cnf_transformation,[],[f90]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1641,plain,
% 3.55/1.12      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.55/1.12      inference(light_normalisation,[status(thm)],[c_1586,c_23]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1810,plain,
% 3.55/1.12      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 3.55/1.12      inference(predicate_to_equality_rev,[status(thm)],[c_1641]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_24,negated_conjecture,
% 3.55/1.12      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.55/1.12      inference(cnf_transformation,[],[f89]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1585,plain,
% 3.55/1.12      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.55/1.12      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1624,plain,
% 3.55/1.12      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.55/1.12      inference(light_normalisation,[status(thm)],[c_1585,c_23]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_1802,plain,
% 3.55/1.12      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 3.55/1.12      inference(predicate_to_equality_rev,[status(thm)],[c_1624]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_999,plain,
% 3.55/1.12      ( sK1 = sK1 ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_970]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_985,plain,
% 3.55/1.12      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.55/1.12      inference(instantiation,[status(thm)],[c_972]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_21,negated_conjecture,
% 3.55/1.12      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.55/1.12      inference(cnf_transformation,[],[f92]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_25,negated_conjecture,
% 3.55/1.12      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.55/1.12      inference(cnf_transformation,[],[f88]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_27,negated_conjecture,
% 3.55/1.12      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.55/1.12      inference(cnf_transformation,[],[f86]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_31,negated_conjecture,
% 3.55/1.12      ( ~ v2_struct_0(sK3) ),
% 3.55/1.12      inference(cnf_transformation,[],[f82]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_33,negated_conjecture,
% 3.55/1.12      ( ~ v2_struct_0(sK2) ),
% 3.55/1.12      inference(cnf_transformation,[],[f80]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_34,negated_conjecture,
% 3.55/1.12      ( l1_pre_topc(sK1) ),
% 3.55/1.12      inference(cnf_transformation,[],[f79]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_35,negated_conjecture,
% 3.55/1.12      ( v2_pre_topc(sK1) ),
% 3.55/1.12      inference(cnf_transformation,[],[f78]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_36,negated_conjecture,
% 3.55/1.12      ( ~ v2_struct_0(sK1) ),
% 3.55/1.12      inference(cnf_transformation,[],[f77]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_38,negated_conjecture,
% 3.55/1.12      ( v2_pre_topc(sK0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f75]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(c_39,negated_conjecture,
% 3.55/1.12      ( ~ v2_struct_0(sK0) ),
% 3.55/1.12      inference(cnf_transformation,[],[f74]) ).
% 3.55/1.12  
% 3.55/1.12  cnf(contradiction,plain,
% 3.55/1.12      ( $false ),
% 3.55/1.12      inference(minisat,
% 3.55/1.12                [status(thm)],
% 3.55/1.12                [c_12340,c_6640,c_6553,c_4192,c_3783,c_3219,c_3198,
% 3.55/1.12                 c_2923,c_2752,c_2552,c_2230,c_2181,c_2130,c_2128,c_2090,
% 3.55/1.12                 c_1889,c_1810,c_1802,c_999,c_985,c_21,c_25,c_26,c_27,
% 3.55/1.12                 c_30,c_31,c_33,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 3.55/1.12  
% 3.55/1.12  
% 3.55/1.12  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/1.12  
% 3.55/1.12  ------                               Statistics
% 3.55/1.12  
% 3.55/1.12  ------ Selected
% 3.55/1.12  
% 3.55/1.12  total_time:                             0.372
% 3.55/1.12  
%------------------------------------------------------------------------------
