%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:38 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  200 (1457 expanded)
%              Number of clauses        :  114 ( 367 expanded)
%              Number of leaves         :   22 ( 604 expanded)
%              Depth                    :   26
%              Number of atoms          : 1160 (18540 expanded)
%              Number of equality atoms :  334 (2831 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f50,f49,f48,f47,f46,f45,f44])).

fof(f89,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f27])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(nnf_transformation,[],[f36])).

fof(f71,plain,(
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

fof(f94,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f83,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1409,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1425,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1409,c_22])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1405,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1420,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2054,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1405,c_1420])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_48,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1577,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1708,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_1709,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1708])).

cnf(c_2260,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2054,c_41,c_48,c_1709])).

cnf(c_4,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_385,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_1395,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_2264,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2260,c_1395])).

cnf(c_12,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_209,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_210,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_468,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_469,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_473,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_28])).

cnf(c_474,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_517,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_474,c_17])).

cnf(c_540,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X5),X6)
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(resolution_lifted,[status(thm)],[c_210,c_517])).

cnf(c_541,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X0),X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_585,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X0),X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_541,c_2,c_5])).

cnf(c_1394,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
    | v3_pre_topc(u1_struct_0(X2),X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_1994,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1394])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3713,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1994,c_42,c_43,c_44])).

cnf(c_3714,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3713])).

cnf(c_1401,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2030,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1401,c_1395])).

cnf(c_3717,plain,
    ( u1_struct_0(X0) != k2_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3714,c_2030,c_2264])).

cnf(c_3722,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_3717])).

cnf(c_3727,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3722,c_2264])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1406,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2184,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2030,c_1406])).

cnf(c_2293,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2184,c_2264])).

cnf(c_11732,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3727,c_47,c_2293])).

cnf(c_11733,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11732])).

cnf(c_11738,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_11733])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1403,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2055,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1420])).

cnf(c_46,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1589,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1713,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1714,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1713])).

cnf(c_2266,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2055,c_41,c_46,c_1714])).

cnf(c_2270,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2266,c_1395])).

cnf(c_11740,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11738,c_2270])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1412,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2700,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1412])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2340,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2270,c_25])).

cnf(c_2701,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2700,c_2270,c_2340])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2973,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_39,c_40,c_41,c_45])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1413,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3028,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2973,c_1413])).

cnf(c_10,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1415,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1422,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1424,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1422,c_0])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1416,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2488,plain,
    ( v3_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_1416])).

cnf(c_2495,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2488,c_2270,c_2340])).

cnf(c_1871,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2069,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2070,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2069])).

cnf(c_2964,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2495,c_40,c_41,c_46,c_1714,c_2070])).

cnf(c_2970,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1424,c_2964])).

cnf(c_3025,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1415,c_2970])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1408,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1423,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1408,c_22])).

cnf(c_2339,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2270,c_1423])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1407,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2295,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2264,c_1407])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_55,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11740,c_3028,c_3025,c_2339,c_2295,c_2070,c_1714,c_55,c_48,c_46,c_45,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.90/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/0.96  
% 3.90/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.96  
% 3.90/0.96  ------  iProver source info
% 3.90/0.96  
% 3.90/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.96  git: non_committed_changes: false
% 3.90/0.96  git: last_make_outside_of_git: false
% 3.90/0.96  
% 3.90/0.96  ------ 
% 3.90/0.96  
% 3.90/0.96  ------ Input Options
% 3.90/0.96  
% 3.90/0.96  --out_options                           all
% 3.90/0.96  --tptp_safe_out                         true
% 3.90/0.96  --problem_path                          ""
% 3.90/0.96  --include_path                          ""
% 3.90/0.96  --clausifier                            res/vclausify_rel
% 3.90/0.96  --clausifier_options                    ""
% 3.90/0.96  --stdin                                 false
% 3.90/0.96  --stats_out                             all
% 3.90/0.96  
% 3.90/0.96  ------ General Options
% 3.90/0.96  
% 3.90/0.96  --fof                                   false
% 3.90/0.96  --time_out_real                         305.
% 3.90/0.96  --time_out_virtual                      -1.
% 3.90/0.96  --symbol_type_check                     false
% 3.90/0.96  --clausify_out                          false
% 3.90/0.96  --sig_cnt_out                           false
% 3.90/0.96  --trig_cnt_out                          false
% 3.90/0.96  --trig_cnt_out_tolerance                1.
% 3.90/0.96  --trig_cnt_out_sk_spl                   false
% 3.90/0.96  --abstr_cl_out                          false
% 3.90/0.96  
% 3.90/0.96  ------ Global Options
% 3.90/0.96  
% 3.90/0.96  --schedule                              default
% 3.90/0.96  --add_important_lit                     false
% 3.90/0.96  --prop_solver_per_cl                    1000
% 3.90/0.96  --min_unsat_core                        false
% 3.90/0.96  --soft_assumptions                      false
% 3.90/0.96  --soft_lemma_size                       3
% 3.90/0.96  --prop_impl_unit_size                   0
% 3.90/0.96  --prop_impl_unit                        []
% 3.90/0.96  --share_sel_clauses                     true
% 3.90/0.96  --reset_solvers                         false
% 3.90/0.96  --bc_imp_inh                            [conj_cone]
% 3.90/0.96  --conj_cone_tolerance                   3.
% 3.90/0.96  --extra_neg_conj                        none
% 3.90/0.96  --large_theory_mode                     true
% 3.90/0.96  --prolific_symb_bound                   200
% 3.90/0.96  --lt_threshold                          2000
% 3.90/0.96  --clause_weak_htbl                      true
% 3.90/0.96  --gc_record_bc_elim                     false
% 3.90/0.96  
% 3.90/0.96  ------ Preprocessing Options
% 3.90/0.96  
% 3.90/0.96  --preprocessing_flag                    true
% 3.90/0.96  --time_out_prep_mult                    0.1
% 3.90/0.96  --splitting_mode                        input
% 3.90/0.96  --splitting_grd                         true
% 3.90/0.96  --splitting_cvd                         false
% 3.90/0.96  --splitting_cvd_svl                     false
% 3.90/0.96  --splitting_nvd                         32
% 3.90/0.96  --sub_typing                            true
% 3.90/0.96  --prep_gs_sim                           true
% 3.90/0.96  --prep_unflatten                        true
% 3.90/0.96  --prep_res_sim                          true
% 3.90/0.96  --prep_upred                            true
% 3.90/0.96  --prep_sem_filter                       exhaustive
% 3.90/0.96  --prep_sem_filter_out                   false
% 3.90/0.96  --pred_elim                             true
% 3.90/0.96  --res_sim_input                         true
% 3.90/0.96  --eq_ax_congr_red                       true
% 3.90/0.96  --pure_diseq_elim                       true
% 3.90/0.96  --brand_transform                       false
% 3.90/0.96  --non_eq_to_eq                          false
% 3.90/0.96  --prep_def_merge                        true
% 3.90/0.96  --prep_def_merge_prop_impl              false
% 3.90/0.96  --prep_def_merge_mbd                    true
% 3.90/0.96  --prep_def_merge_tr_red                 false
% 3.90/0.96  --prep_def_merge_tr_cl                  false
% 3.90/0.96  --smt_preprocessing                     true
% 3.90/0.96  --smt_ac_axioms                         fast
% 3.90/0.96  --preprocessed_out                      false
% 3.90/0.96  --preprocessed_stats                    false
% 3.90/0.96  
% 3.90/0.96  ------ Abstraction refinement Options
% 3.90/0.96  
% 3.90/0.96  --abstr_ref                             []
% 3.90/0.96  --abstr_ref_prep                        false
% 3.90/0.96  --abstr_ref_until_sat                   false
% 3.90/0.96  --abstr_ref_sig_restrict                funpre
% 3.90/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/0.96  --abstr_ref_under                       []
% 3.90/0.96  
% 3.90/0.96  ------ SAT Options
% 3.90/0.96  
% 3.90/0.96  --sat_mode                              false
% 3.90/0.96  --sat_fm_restart_options                ""
% 3.90/0.96  --sat_gr_def                            false
% 3.90/0.96  --sat_epr_types                         true
% 3.90/0.96  --sat_non_cyclic_types                  false
% 3.90/0.96  --sat_finite_models                     false
% 3.90/0.96  --sat_fm_lemmas                         false
% 3.90/0.96  --sat_fm_prep                           false
% 3.90/0.96  --sat_fm_uc_incr                        true
% 3.90/0.96  --sat_out_model                         small
% 3.90/0.96  --sat_out_clauses                       false
% 3.90/0.96  
% 3.90/0.96  ------ QBF Options
% 3.90/0.96  
% 3.90/0.96  --qbf_mode                              false
% 3.90/0.96  --qbf_elim_univ                         false
% 3.90/0.96  --qbf_dom_inst                          none
% 3.90/0.96  --qbf_dom_pre_inst                      false
% 3.90/0.96  --qbf_sk_in                             false
% 3.90/0.96  --qbf_pred_elim                         true
% 3.90/0.96  --qbf_split                             512
% 3.90/0.96  
% 3.90/0.96  ------ BMC1 Options
% 3.90/0.96  
% 3.90/0.96  --bmc1_incremental                      false
% 3.90/0.96  --bmc1_axioms                           reachable_all
% 3.90/0.96  --bmc1_min_bound                        0
% 3.90/0.96  --bmc1_max_bound                        -1
% 3.90/0.96  --bmc1_max_bound_default                -1
% 3.90/0.96  --bmc1_symbol_reachability              true
% 3.90/0.96  --bmc1_property_lemmas                  false
% 3.90/0.96  --bmc1_k_induction                      false
% 3.90/0.96  --bmc1_non_equiv_states                 false
% 3.90/0.96  --bmc1_deadlock                         false
% 3.90/0.96  --bmc1_ucm                              false
% 3.90/0.96  --bmc1_add_unsat_core                   none
% 3.90/0.96  --bmc1_unsat_core_children              false
% 3.90/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/0.96  --bmc1_out_stat                         full
% 3.90/0.96  --bmc1_ground_init                      false
% 3.90/0.96  --bmc1_pre_inst_next_state              false
% 3.90/0.96  --bmc1_pre_inst_state                   false
% 3.90/0.96  --bmc1_pre_inst_reach_state             false
% 3.90/0.96  --bmc1_out_unsat_core                   false
% 3.90/0.96  --bmc1_aig_witness_out                  false
% 3.90/0.96  --bmc1_verbose                          false
% 3.90/0.96  --bmc1_dump_clauses_tptp                false
% 3.90/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.90/0.96  --bmc1_dump_file                        -
% 3.90/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.90/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.90/0.96  --bmc1_ucm_extend_mode                  1
% 3.90/0.96  --bmc1_ucm_init_mode                    2
% 3.90/0.96  --bmc1_ucm_cone_mode                    none
% 3.90/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.90/0.96  --bmc1_ucm_relax_model                  4
% 3.90/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.90/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/0.96  --bmc1_ucm_layered_model                none
% 3.90/0.96  --bmc1_ucm_max_lemma_size               10
% 3.90/0.96  
% 3.90/0.96  ------ AIG Options
% 3.90/0.96  
% 3.90/0.96  --aig_mode                              false
% 3.90/0.96  
% 3.90/0.96  ------ Instantiation Options
% 3.90/0.96  
% 3.90/0.96  --instantiation_flag                    true
% 3.90/0.96  --inst_sos_flag                         true
% 3.90/0.96  --inst_sos_phase                        true
% 3.90/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/0.96  --inst_lit_sel_side                     num_symb
% 3.90/0.96  --inst_solver_per_active                1400
% 3.90/0.96  --inst_solver_calls_frac                1.
% 3.90/0.96  --inst_passive_queue_type               priority_queues
% 3.90/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/0.96  --inst_passive_queues_freq              [25;2]
% 3.90/0.96  --inst_dismatching                      true
% 3.90/0.96  --inst_eager_unprocessed_to_passive     true
% 3.90/0.96  --inst_prop_sim_given                   true
% 3.90/0.96  --inst_prop_sim_new                     false
% 3.90/0.96  --inst_subs_new                         false
% 3.90/0.96  --inst_eq_res_simp                      false
% 3.90/0.96  --inst_subs_given                       false
% 3.90/0.96  --inst_orphan_elimination               true
% 3.90/0.96  --inst_learning_loop_flag               true
% 3.90/0.96  --inst_learning_start                   3000
% 3.90/0.96  --inst_learning_factor                  2
% 3.90/0.96  --inst_start_prop_sim_after_learn       3
% 3.90/0.96  --inst_sel_renew                        solver
% 3.90/0.96  --inst_lit_activity_flag                true
% 3.90/0.96  --inst_restr_to_given                   false
% 3.90/0.96  --inst_activity_threshold               500
% 3.90/0.96  --inst_out_proof                        true
% 3.90/0.96  
% 3.90/0.96  ------ Resolution Options
% 3.90/0.96  
% 3.90/0.96  --resolution_flag                       true
% 3.90/0.96  --res_lit_sel                           adaptive
% 3.90/0.96  --res_lit_sel_side                      none
% 3.90/0.96  --res_ordering                          kbo
% 3.90/0.96  --res_to_prop_solver                    active
% 3.90/0.96  --res_prop_simpl_new                    false
% 3.90/0.96  --res_prop_simpl_given                  true
% 3.90/0.96  --res_passive_queue_type                priority_queues
% 3.90/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/0.96  --res_passive_queues_freq               [15;5]
% 3.90/0.96  --res_forward_subs                      full
% 3.90/0.96  --res_backward_subs                     full
% 3.90/0.96  --res_forward_subs_resolution           true
% 3.90/0.96  --res_backward_subs_resolution          true
% 3.90/0.96  --res_orphan_elimination                true
% 3.90/0.96  --res_time_limit                        2.
% 3.90/0.96  --res_out_proof                         true
% 3.90/0.96  
% 3.90/0.96  ------ Superposition Options
% 3.90/0.96  
% 3.90/0.96  --superposition_flag                    true
% 3.90/0.96  --sup_passive_queue_type                priority_queues
% 3.90/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.90/0.96  --demod_completeness_check              fast
% 3.90/0.96  --demod_use_ground                      true
% 3.90/0.96  --sup_to_prop_solver                    passive
% 3.90/0.96  --sup_prop_simpl_new                    true
% 3.90/0.96  --sup_prop_simpl_given                  true
% 3.90/0.96  --sup_fun_splitting                     true
% 3.90/0.96  --sup_smt_interval                      50000
% 3.90/0.96  
% 3.90/0.96  ------ Superposition Simplification Setup
% 3.90/0.96  
% 3.90/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.90/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.90/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.90/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.90/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.90/0.96  --sup_immed_triv                        [TrivRules]
% 3.90/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.96  --sup_immed_bw_main                     []
% 3.90/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.90/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.96  --sup_input_bw                          []
% 3.90/0.96  
% 3.90/0.96  ------ Combination Options
% 3.90/0.96  
% 3.90/0.96  --comb_res_mult                         3
% 3.90/0.96  --comb_sup_mult                         2
% 3.90/0.96  --comb_inst_mult                        10
% 3.90/0.96  
% 3.90/0.96  ------ Debug Options
% 3.90/0.96  
% 3.90/0.96  --dbg_backtrace                         false
% 3.90/0.96  --dbg_dump_prop_clauses                 false
% 3.90/0.96  --dbg_dump_prop_clauses_file            -
% 3.90/0.96  --dbg_out_stat                          false
% 3.90/0.96  ------ Parsing...
% 3.90/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.96  
% 3.90/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.90/0.96  
% 3.90/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.96  
% 3.90/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.96  ------ Proving...
% 3.90/0.96  ------ Problem Properties 
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  clauses                                 33
% 3.90/0.96  conjectures                             17
% 3.90/0.96  EPR                                     15
% 3.90/0.96  Horn                                    29
% 3.90/0.96  unary                                   19
% 3.90/0.96  binary                                  1
% 3.90/0.96  lits                                    109
% 3.90/0.96  lits eq                                 9
% 3.90/0.96  fd_pure                                 0
% 3.90/0.96  fd_pseudo                               0
% 3.90/0.96  fd_cond                                 0
% 3.90/0.96  fd_pseudo_cond                          0
% 3.90/0.96  AC symbols                              0
% 3.90/0.96  
% 3.90/0.96  ------ Schedule dynamic 5 is on 
% 3.90/0.96  
% 3.90/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  ------ 
% 3.90/0.96  Current options:
% 3.90/0.96  ------ 
% 3.90/0.96  
% 3.90/0.96  ------ Input Options
% 3.90/0.96  
% 3.90/0.96  --out_options                           all
% 3.90/0.96  --tptp_safe_out                         true
% 3.90/0.96  --problem_path                          ""
% 3.90/0.96  --include_path                          ""
% 3.90/0.96  --clausifier                            res/vclausify_rel
% 3.90/0.96  --clausifier_options                    ""
% 3.90/0.96  --stdin                                 false
% 3.90/0.96  --stats_out                             all
% 3.90/0.96  
% 3.90/0.96  ------ General Options
% 3.90/0.96  
% 3.90/0.96  --fof                                   false
% 3.90/0.96  --time_out_real                         305.
% 3.90/0.96  --time_out_virtual                      -1.
% 3.90/0.96  --symbol_type_check                     false
% 3.90/0.96  --clausify_out                          false
% 3.90/0.96  --sig_cnt_out                           false
% 3.90/0.96  --trig_cnt_out                          false
% 3.90/0.96  --trig_cnt_out_tolerance                1.
% 3.90/0.96  --trig_cnt_out_sk_spl                   false
% 3.90/0.96  --abstr_cl_out                          false
% 3.90/0.96  
% 3.90/0.96  ------ Global Options
% 3.90/0.96  
% 3.90/0.96  --schedule                              default
% 3.90/0.96  --add_important_lit                     false
% 3.90/0.96  --prop_solver_per_cl                    1000
% 3.90/0.96  --min_unsat_core                        false
% 3.90/0.96  --soft_assumptions                      false
% 3.90/0.96  --soft_lemma_size                       3
% 3.90/0.96  --prop_impl_unit_size                   0
% 3.90/0.96  --prop_impl_unit                        []
% 3.90/0.96  --share_sel_clauses                     true
% 3.90/0.96  --reset_solvers                         false
% 3.90/0.96  --bc_imp_inh                            [conj_cone]
% 3.90/0.96  --conj_cone_tolerance                   3.
% 3.90/0.96  --extra_neg_conj                        none
% 3.90/0.96  --large_theory_mode                     true
% 3.90/0.96  --prolific_symb_bound                   200
% 3.90/0.96  --lt_threshold                          2000
% 3.90/0.96  --clause_weak_htbl                      true
% 3.90/0.96  --gc_record_bc_elim                     false
% 3.90/0.96  
% 3.90/0.96  ------ Preprocessing Options
% 3.90/0.96  
% 3.90/0.96  --preprocessing_flag                    true
% 3.90/0.96  --time_out_prep_mult                    0.1
% 3.90/0.96  --splitting_mode                        input
% 3.90/0.96  --splitting_grd                         true
% 3.90/0.96  --splitting_cvd                         false
% 3.90/0.96  --splitting_cvd_svl                     false
% 3.90/0.96  --splitting_nvd                         32
% 3.90/0.96  --sub_typing                            true
% 3.90/0.96  --prep_gs_sim                           true
% 3.90/0.96  --prep_unflatten                        true
% 3.90/0.96  --prep_res_sim                          true
% 3.90/0.96  --prep_upred                            true
% 3.90/0.96  --prep_sem_filter                       exhaustive
% 3.90/0.96  --prep_sem_filter_out                   false
% 3.90/0.96  --pred_elim                             true
% 3.90/0.96  --res_sim_input                         true
% 3.90/0.96  --eq_ax_congr_red                       true
% 3.90/0.96  --pure_diseq_elim                       true
% 3.90/0.96  --brand_transform                       false
% 3.90/0.96  --non_eq_to_eq                          false
% 3.90/0.96  --prep_def_merge                        true
% 3.90/0.96  --prep_def_merge_prop_impl              false
% 3.90/0.96  --prep_def_merge_mbd                    true
% 3.90/0.96  --prep_def_merge_tr_red                 false
% 3.90/0.96  --prep_def_merge_tr_cl                  false
% 3.90/0.96  --smt_preprocessing                     true
% 3.90/0.96  --smt_ac_axioms                         fast
% 3.90/0.96  --preprocessed_out                      false
% 3.90/0.96  --preprocessed_stats                    false
% 3.90/0.96  
% 3.90/0.96  ------ Abstraction refinement Options
% 3.90/0.96  
% 3.90/0.96  --abstr_ref                             []
% 3.90/0.96  --abstr_ref_prep                        false
% 3.90/0.96  --abstr_ref_until_sat                   false
% 3.90/0.96  --abstr_ref_sig_restrict                funpre
% 3.90/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/0.96  --abstr_ref_under                       []
% 3.90/0.96  
% 3.90/0.96  ------ SAT Options
% 3.90/0.96  
% 3.90/0.96  --sat_mode                              false
% 3.90/0.96  --sat_fm_restart_options                ""
% 3.90/0.96  --sat_gr_def                            false
% 3.90/0.96  --sat_epr_types                         true
% 3.90/0.96  --sat_non_cyclic_types                  false
% 3.90/0.96  --sat_finite_models                     false
% 3.90/0.96  --sat_fm_lemmas                         false
% 3.90/0.96  --sat_fm_prep                           false
% 3.90/0.96  --sat_fm_uc_incr                        true
% 3.90/0.96  --sat_out_model                         small
% 3.90/0.96  --sat_out_clauses                       false
% 3.90/0.96  
% 3.90/0.96  ------ QBF Options
% 3.90/0.96  
% 3.90/0.96  --qbf_mode                              false
% 3.90/0.96  --qbf_elim_univ                         false
% 3.90/0.96  --qbf_dom_inst                          none
% 3.90/0.96  --qbf_dom_pre_inst                      false
% 3.90/0.96  --qbf_sk_in                             false
% 3.90/0.96  --qbf_pred_elim                         true
% 3.90/0.96  --qbf_split                             512
% 3.90/0.96  
% 3.90/0.96  ------ BMC1 Options
% 3.90/0.96  
% 3.90/0.96  --bmc1_incremental                      false
% 3.90/0.96  --bmc1_axioms                           reachable_all
% 3.90/0.96  --bmc1_min_bound                        0
% 3.90/0.96  --bmc1_max_bound                        -1
% 3.90/0.96  --bmc1_max_bound_default                -1
% 3.90/0.96  --bmc1_symbol_reachability              true
% 3.90/0.96  --bmc1_property_lemmas                  false
% 3.90/0.96  --bmc1_k_induction                      false
% 3.90/0.96  --bmc1_non_equiv_states                 false
% 3.90/0.96  --bmc1_deadlock                         false
% 3.90/0.96  --bmc1_ucm                              false
% 3.90/0.96  --bmc1_add_unsat_core                   none
% 3.90/0.96  --bmc1_unsat_core_children              false
% 3.90/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/0.96  --bmc1_out_stat                         full
% 3.90/0.96  --bmc1_ground_init                      false
% 3.90/0.96  --bmc1_pre_inst_next_state              false
% 3.90/0.96  --bmc1_pre_inst_state                   false
% 3.90/0.96  --bmc1_pre_inst_reach_state             false
% 3.90/0.96  --bmc1_out_unsat_core                   false
% 3.90/0.96  --bmc1_aig_witness_out                  false
% 3.90/0.96  --bmc1_verbose                          false
% 3.90/0.96  --bmc1_dump_clauses_tptp                false
% 3.90/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.90/0.96  --bmc1_dump_file                        -
% 3.90/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.90/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.90/0.96  --bmc1_ucm_extend_mode                  1
% 3.90/0.96  --bmc1_ucm_init_mode                    2
% 3.90/0.96  --bmc1_ucm_cone_mode                    none
% 3.90/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.90/0.96  --bmc1_ucm_relax_model                  4
% 3.90/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.90/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/0.96  --bmc1_ucm_layered_model                none
% 3.90/0.96  --bmc1_ucm_max_lemma_size               10
% 3.90/0.96  
% 3.90/0.96  ------ AIG Options
% 3.90/0.96  
% 3.90/0.96  --aig_mode                              false
% 3.90/0.96  
% 3.90/0.96  ------ Instantiation Options
% 3.90/0.96  
% 3.90/0.96  --instantiation_flag                    true
% 3.90/0.96  --inst_sos_flag                         true
% 3.90/0.96  --inst_sos_phase                        true
% 3.90/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/0.96  --inst_lit_sel_side                     none
% 3.90/0.96  --inst_solver_per_active                1400
% 3.90/0.96  --inst_solver_calls_frac                1.
% 3.90/0.96  --inst_passive_queue_type               priority_queues
% 3.90/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/0.96  --inst_passive_queues_freq              [25;2]
% 3.90/0.96  --inst_dismatching                      true
% 3.90/0.96  --inst_eager_unprocessed_to_passive     true
% 3.90/0.96  --inst_prop_sim_given                   true
% 3.90/0.96  --inst_prop_sim_new                     false
% 3.90/0.96  --inst_subs_new                         false
% 3.90/0.96  --inst_eq_res_simp                      false
% 3.90/0.96  --inst_subs_given                       false
% 3.90/0.96  --inst_orphan_elimination               true
% 3.90/0.96  --inst_learning_loop_flag               true
% 3.90/0.96  --inst_learning_start                   3000
% 3.90/0.96  --inst_learning_factor                  2
% 3.90/0.96  --inst_start_prop_sim_after_learn       3
% 3.90/0.96  --inst_sel_renew                        solver
% 3.90/0.96  --inst_lit_activity_flag                true
% 3.90/0.96  --inst_restr_to_given                   false
% 3.90/0.96  --inst_activity_threshold               500
% 3.90/0.96  --inst_out_proof                        true
% 3.90/0.96  
% 3.90/0.96  ------ Resolution Options
% 3.90/0.96  
% 3.90/0.96  --resolution_flag                       false
% 3.90/0.96  --res_lit_sel                           adaptive
% 3.90/0.96  --res_lit_sel_side                      none
% 3.90/0.96  --res_ordering                          kbo
% 3.90/0.96  --res_to_prop_solver                    active
% 3.90/0.96  --res_prop_simpl_new                    false
% 3.90/0.96  --res_prop_simpl_given                  true
% 3.90/0.96  --res_passive_queue_type                priority_queues
% 3.90/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/0.96  --res_passive_queues_freq               [15;5]
% 3.90/0.96  --res_forward_subs                      full
% 3.90/0.96  --res_backward_subs                     full
% 3.90/0.96  --res_forward_subs_resolution           true
% 3.90/0.96  --res_backward_subs_resolution          true
% 3.90/0.96  --res_orphan_elimination                true
% 3.90/0.96  --res_time_limit                        2.
% 3.90/0.96  --res_out_proof                         true
% 3.90/0.96  
% 3.90/0.96  ------ Superposition Options
% 3.90/0.96  
% 3.90/0.96  --superposition_flag                    true
% 3.90/0.96  --sup_passive_queue_type                priority_queues
% 3.90/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.90/0.96  --demod_completeness_check              fast
% 3.90/0.96  --demod_use_ground                      true
% 3.90/0.96  --sup_to_prop_solver                    passive
% 3.90/0.96  --sup_prop_simpl_new                    true
% 3.90/0.96  --sup_prop_simpl_given                  true
% 3.90/0.96  --sup_fun_splitting                     true
% 3.90/0.96  --sup_smt_interval                      50000
% 3.90/0.96  
% 3.90/0.96  ------ Superposition Simplification Setup
% 3.90/0.96  
% 3.90/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.90/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.90/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.90/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.90/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.90/0.96  --sup_immed_triv                        [TrivRules]
% 3.90/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.96  --sup_immed_bw_main                     []
% 3.90/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.90/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.96  --sup_input_bw                          []
% 3.90/0.96  
% 3.90/0.96  ------ Combination Options
% 3.90/0.96  
% 3.90/0.96  --comb_res_mult                         3
% 3.90/0.96  --comb_sup_mult                         2
% 3.90/0.96  --comb_inst_mult                        10
% 3.90/0.96  
% 3.90/0.96  ------ Debug Options
% 3.90/0.96  
% 3.90/0.96  --dbg_backtrace                         false
% 3.90/0.96  --dbg_dump_prop_clauses                 false
% 3.90/0.96  --dbg_dump_prop_clauses_file            -
% 3.90/0.96  --dbg_out_stat                          false
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  ------ Proving...
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  % SZS status Theorem for theBenchmark.p
% 3.90/0.96  
% 3.90/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/0.96  
% 3.90/0.96  fof(f15,conjecture,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f16,negated_conjecture,(
% 3.90/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.90/0.96    inference(negated_conjecture,[],[f15])).
% 3.90/0.96  
% 3.90/0.96  fof(f37,plain,(
% 3.90/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f16])).
% 3.90/0.96  
% 3.90/0.96  fof(f38,plain,(
% 3.90/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.90/0.96    inference(flattening,[],[f37])).
% 3.90/0.96  
% 3.90/0.96  fof(f50,plain,(
% 3.90/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.90/0.96    introduced(choice_axiom,[])).
% 3.90/0.96  
% 3.90/0.96  fof(f49,plain,(
% 3.90/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.90/0.96    introduced(choice_axiom,[])).
% 3.90/0.96  
% 3.90/0.96  fof(f48,plain,(
% 3.90/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.90/0.96    introduced(choice_axiom,[])).
% 3.90/0.96  
% 3.90/0.96  fof(f47,plain,(
% 3.90/0.96    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.90/0.96    introduced(choice_axiom,[])).
% 3.90/0.96  
% 3.90/0.96  fof(f46,plain,(
% 3.90/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.90/0.96    introduced(choice_axiom,[])).
% 3.90/0.96  
% 3.90/0.96  fof(f45,plain,(
% 3.90/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.90/0.96    introduced(choice_axiom,[])).
% 3.90/0.96  
% 3.90/0.96  fof(f44,plain,(
% 3.90/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.90/0.96    introduced(choice_axiom,[])).
% 3.90/0.96  
% 3.90/0.96  fof(f51,plain,(
% 3.90/0.96    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.90/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f50,f49,f48,f47,f46,f45,f44])).
% 3.90/0.96  
% 3.90/0.96  fof(f89,plain,(
% 3.90/0.96    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f88,plain,(
% 3.90/0.96    sK5 = sK6),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f81,plain,(
% 3.90/0.96    m1_pre_topc(sK3,sK0)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f6,axiom,(
% 3.90/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f21,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.90/0.96    inference(ennf_transformation,[],[f6])).
% 3.90/0.96  
% 3.90/0.96  fof(f57,plain,(
% 3.90/0.96    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f21])).
% 3.90/0.96  
% 3.90/0.96  fof(f74,plain,(
% 3.90/0.96    l1_pre_topc(sK0)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f5,axiom,(
% 3.90/0.96    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f20,plain,(
% 3.90/0.96    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.90/0.96    inference(ennf_transformation,[],[f5])).
% 3.90/0.96  
% 3.90/0.96  fof(f56,plain,(
% 3.90/0.96    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f20])).
% 3.90/0.96  
% 3.90/0.96  fof(f4,axiom,(
% 3.90/0.96    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f19,plain,(
% 3.90/0.96    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.90/0.96    inference(ennf_transformation,[],[f4])).
% 3.90/0.96  
% 3.90/0.96  fof(f55,plain,(
% 3.90/0.96    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f19])).
% 3.90/0.96  
% 3.90/0.96  fof(f9,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f26,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f9])).
% 3.90/0.96  
% 3.90/0.96  fof(f27,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(flattening,[],[f26])).
% 3.90/0.96  
% 3.90/0.96  fof(f41,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(nnf_transformation,[],[f27])).
% 3.90/0.96  
% 3.90/0.96  fof(f42,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(flattening,[],[f41])).
% 3.90/0.96  
% 3.90/0.96  fof(f64,plain,(
% 3.90/0.96    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f42])).
% 3.90/0.96  
% 3.90/0.96  fof(f92,plain,(
% 3.90/0.96    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.96    inference(equality_resolution,[],[f64])).
% 3.90/0.96  
% 3.90/0.96  fof(f10,axiom,(
% 3.90/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f28,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.90/0.96    inference(ennf_transformation,[],[f10])).
% 3.90/0.96  
% 3.90/0.96  fof(f66,plain,(
% 3.90/0.96    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f28])).
% 3.90/0.96  
% 3.90/0.96  fof(f14,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f35,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f14])).
% 3.90/0.96  
% 3.90/0.96  fof(f36,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.90/0.96    inference(flattening,[],[f35])).
% 3.90/0.96  
% 3.90/0.96  fof(f43,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.90/0.96    inference(nnf_transformation,[],[f36])).
% 3.90/0.96  
% 3.90/0.96  fof(f71,plain,(
% 3.90/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f43])).
% 3.90/0.96  
% 3.90/0.96  fof(f94,plain,(
% 3.90/0.96    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.90/0.96    inference(equality_resolution,[],[f71])).
% 3.90/0.96  
% 3.90/0.96  fof(f83,plain,(
% 3.90/0.96    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f82,plain,(
% 3.90/0.96    v1_funct_1(sK4)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f13,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f33,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f13])).
% 3.90/0.96  
% 3.90/0.96  fof(f34,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(flattening,[],[f33])).
% 3.90/0.96  
% 3.90/0.96  fof(f69,plain,(
% 3.90/0.96    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f34])).
% 3.90/0.96  
% 3.90/0.96  fof(f3,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f17,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f3])).
% 3.90/0.96  
% 3.90/0.96  fof(f18,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(flattening,[],[f17])).
% 3.90/0.96  
% 3.90/0.96  fof(f54,plain,(
% 3.90/0.96    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f18])).
% 3.90/0.96  
% 3.90/0.96  fof(f75,plain,(
% 3.90/0.96    ~v2_struct_0(sK1)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f76,plain,(
% 3.90/0.96    v2_pre_topc(sK1)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f77,plain,(
% 3.90/0.96    l1_pre_topc(sK1)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f80,plain,(
% 3.90/0.96    ~v2_struct_0(sK3)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f84,plain,(
% 3.90/0.96    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f79,plain,(
% 3.90/0.96    m1_pre_topc(sK2,sK0)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f12,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f31,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f12])).
% 3.90/0.96  
% 3.90/0.96  fof(f32,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.90/0.96    inference(flattening,[],[f31])).
% 3.90/0.96  
% 3.90/0.96  fof(f68,plain,(
% 3.90/0.96    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f32])).
% 3.90/0.96  
% 3.90/0.96  fof(f85,plain,(
% 3.90/0.96    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f72,plain,(
% 3.90/0.96    ~v2_struct_0(sK0)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f73,plain,(
% 3.90/0.96    v2_pre_topc(sK0)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f78,plain,(
% 3.90/0.96    ~v2_struct_0(sK2)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f11,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f29,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f11])).
% 3.90/0.96  
% 3.90/0.96  fof(f30,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.90/0.96    inference(flattening,[],[f29])).
% 3.90/0.96  
% 3.90/0.96  fof(f67,plain,(
% 3.90/0.96    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f30])).
% 3.90/0.96  
% 3.90/0.96  fof(f8,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f24,plain,(
% 3.90/0.96    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f8])).
% 3.90/0.96  
% 3.90/0.96  fof(f25,plain,(
% 3.90/0.96    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(flattening,[],[f24])).
% 3.90/0.96  
% 3.90/0.96  fof(f62,plain,(
% 3.90/0.96    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f25])).
% 3.90/0.96  
% 3.90/0.96  fof(f2,axiom,(
% 3.90/0.96    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f53,plain,(
% 3.90/0.96    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.90/0.96    inference(cnf_transformation,[],[f2])).
% 3.90/0.96  
% 3.90/0.96  fof(f1,axiom,(
% 3.90/0.96    ! [X0] : k2_subset_1(X0) = X0),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f52,plain,(
% 3.90/0.96    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.90/0.96    inference(cnf_transformation,[],[f1])).
% 3.90/0.96  
% 3.90/0.96  fof(f7,axiom,(
% 3.90/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.90/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.96  
% 3.90/0.96  fof(f22,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.96    inference(ennf_transformation,[],[f7])).
% 3.90/0.96  
% 3.90/0.96  fof(f23,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(flattening,[],[f22])).
% 3.90/0.96  
% 3.90/0.96  fof(f39,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(nnf_transformation,[],[f23])).
% 3.90/0.96  
% 3.90/0.96  fof(f40,plain,(
% 3.90/0.96    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.96    inference(flattening,[],[f39])).
% 3.90/0.96  
% 3.90/0.96  fof(f58,plain,(
% 3.90/0.96    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.96    inference(cnf_transformation,[],[f40])).
% 3.90/0.96  
% 3.90/0.96  fof(f87,plain,(
% 3.90/0.96    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f86,plain,(
% 3.90/0.96    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  fof(f90,plain,(
% 3.90/0.96    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.90/0.96    inference(cnf_transformation,[],[f51])).
% 3.90/0.96  
% 3.90/0.96  cnf(c_21,negated_conjecture,
% 3.90/0.96      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.90/0.96      inference(cnf_transformation,[],[f89]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1409,plain,
% 3.90/0.96      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_22,negated_conjecture,
% 3.90/0.96      ( sK5 = sK6 ),
% 3.90/0.96      inference(cnf_transformation,[],[f88]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1425,plain,
% 3.90/0.96      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_1409,c_22]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_29,negated_conjecture,
% 3.90/0.96      ( m1_pre_topc(sK3,sK0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1405,plain,
% 3.90/0.96      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_5,plain,
% 3.90/0.96      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1420,plain,
% 3.90/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | l1_pre_topc(X0) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2054,plain,
% 3.90/0.96      ( l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK3) = iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_1405,c_1420]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_36,negated_conjecture,
% 3.90/0.96      ( l1_pre_topc(sK0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f74]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_41,plain,
% 3.90/0.96      ( l1_pre_topc(sK0) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_48,plain,
% 3.90/0.96      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1577,plain,
% 3.90/0.96      ( ~ m1_pre_topc(sK3,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK3) ),
% 3.90/0.96      inference(instantiation,[status(thm)],[c_5]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1708,plain,
% 3.90/0.96      ( ~ m1_pre_topc(sK3,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.90/0.96      inference(instantiation,[status(thm)],[c_1577]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1709,plain,
% 3.90/0.96      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK3) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_1708]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2260,plain,
% 3.90/0.96      ( l1_pre_topc(sK3) = iProver_top ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_2054,c_41,c_48,c_1709]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_4,plain,
% 3.90/0.96      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3,plain,
% 3.90/0.96      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f55]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_385,plain,
% 3.90/0.96      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.90/0.96      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1395,plain,
% 3.90/0.96      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.90/0.96      | l1_pre_topc(X0) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2264,plain,
% 3.90/0.96      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_2260,c_1395]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_12,plain,
% 3.90/0.96      ( v1_tsep_1(X0,X1)
% 3.90/0.96      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.90/0.96      | ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f92]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_14,plain,
% 3.90/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.96      | ~ l1_pre_topc(X1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_209,plain,
% 3.90/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.90/0.96      | v1_tsep_1(X0,X1)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1) ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_12,c_14]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_210,plain,
% 3.90/0.96      ( v1_tsep_1(X0,X1)
% 3.90/0.96      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.90/0.96      | ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1) ),
% 3.90/0.96      inference(renaming,[status(thm)],[c_209]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_18,plain,
% 3.90/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 3.90/0.96      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.90/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.90/0.96      | ~ v1_tsep_1(X4,X0)
% 3.90/0.96      | ~ m1_pre_topc(X4,X5)
% 3.90/0.96      | ~ m1_pre_topc(X4,X0)
% 3.90/0.96      | ~ m1_pre_topc(X0,X5)
% 3.90/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.90/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.90/0.96      | ~ v1_funct_1(X2)
% 3.90/0.96      | v2_struct_0(X5)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X4)
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | ~ l1_pre_topc(X5)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X5)
% 3.90/0.96      | ~ v2_pre_topc(X1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f94]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_27,negated_conjecture,
% 3.90/0.96      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.90/0.96      inference(cnf_transformation,[],[f83]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_468,plain,
% 3.90/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 3.90/0.96      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.90/0.96      | ~ v1_tsep_1(X4,X0)
% 3.90/0.96      | ~ m1_pre_topc(X4,X5)
% 3.90/0.96      | ~ m1_pre_topc(X4,X0)
% 3.90/0.96      | ~ m1_pre_topc(X0,X5)
% 3.90/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.90/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.90/0.96      | ~ v1_funct_1(X2)
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X5)
% 3.90/0.96      | v2_struct_0(X4)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ l1_pre_topc(X5)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X5)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.90/0.96      | sK4 != X2 ),
% 3.90/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_469,plain,
% 3.90/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.90/0.96      | r1_tmap_1(X3,X1,sK4,X4)
% 3.90/0.96      | ~ v1_tsep_1(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X0,X2)
% 3.90/0.96      | ~ m1_pre_topc(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X3,X2)
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.90/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.90/0.96      | ~ v1_funct_1(sK4)
% 3.90/0.96      | v2_struct_0(X3)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ l1_pre_topc(X2)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X2)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.90/0.96      inference(unflattening,[status(thm)],[c_468]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_28,negated_conjecture,
% 3.90/0.96      ( v1_funct_1(sK4) ),
% 3.90/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_473,plain,
% 3.90/0.96      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_pre_topc(X3,X2)
% 3.90/0.96      | ~ m1_pre_topc(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X0,X2)
% 3.90/0.96      | ~ v1_tsep_1(X0,X3)
% 3.90/0.96      | r1_tmap_1(X3,X1,sK4,X4)
% 3.90/0.96      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.90/0.96      | v2_struct_0(X3)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ l1_pre_topc(X2)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X2)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_469,c_28]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_474,plain,
% 3.90/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.90/0.96      | r1_tmap_1(X3,X1,sK4,X4)
% 3.90/0.96      | ~ v1_tsep_1(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X0,X2)
% 3.90/0.96      | ~ m1_pre_topc(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X3,X2)
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.90/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | v2_struct_0(X3)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ l1_pre_topc(X2)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X2)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.90/0.96      inference(renaming,[status(thm)],[c_473]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_17,plain,
% 3.90/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | ~ m1_pre_topc(X2,X0)
% 3.90/0.96      | m1_pre_topc(X2,X1)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_517,plain,
% 3.90/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.90/0.96      | r1_tmap_1(X3,X1,sK4,X4)
% 3.90/0.96      | ~ v1_tsep_1(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X3,X2)
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.90/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | v2_struct_0(X3)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ l1_pre_topc(X2)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X2)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.90/0.96      inference(forward_subsumption_resolution,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_474,c_17]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_540,plain,
% 3.90/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.90/0.96      | r1_tmap_1(X3,X1,sK4,X4)
% 3.90/0.96      | ~ v3_pre_topc(u1_struct_0(X5),X6)
% 3.90/0.96      | ~ m1_pre_topc(X5,X6)
% 3.90/0.96      | ~ m1_pre_topc(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X3,X2)
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.90/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | v2_struct_0(X3)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | ~ l1_pre_topc(X6)
% 3.90/0.96      | ~ l1_pre_topc(X2)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X6)
% 3.90/0.96      | ~ v2_pre_topc(X2)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | X0 != X5
% 3.90/0.96      | X3 != X6
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.90/0.96      inference(resolution_lifted,[status(thm)],[c_210,c_517]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_541,plain,
% 3.90/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.90/0.96      | r1_tmap_1(X3,X1,sK4,X4)
% 3.90/0.96      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 3.90/0.96      | ~ m1_pre_topc(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X3,X2)
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.90/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | v2_struct_0(X3)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ l1_pre_topc(X2)
% 3.90/0.96      | ~ l1_pre_topc(X3)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X2)
% 3.90/0.96      | ~ v2_pre_topc(X3)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.90/0.96      inference(unflattening,[status(thm)],[c_540]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2,plain,
% 3.90/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | v2_pre_topc(X0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_585,plain,
% 3.90/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.90/0.96      | r1_tmap_1(X3,X1,sK4,X4)
% 3.90/0.96      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 3.90/0.96      | ~ m1_pre_topc(X0,X3)
% 3.90/0.96      | ~ m1_pre_topc(X3,X2)
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.90/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.90/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | v2_struct_0(X3)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ l1_pre_topc(X2)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X2)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.90/0.96      inference(forward_subsumption_resolution,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_541,c_2,c_5]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1394,plain,
% 3.90/0.96      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.90/0.96      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.90/0.96      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
% 3.90/0.96      | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X2),X1) != iProver_top
% 3.90/0.96      | m1_pre_topc(X2,X1) != iProver_top
% 3.90/0.96      | m1_pre_topc(X1,X3) != iProver_top
% 3.90/0.96      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.90/0.96      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(X2) = iProver_top
% 3.90/0.96      | v2_struct_0(X3) = iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | l1_pre_topc(X0) != iProver_top
% 3.90/0.96      | l1_pre_topc(X3) != iProver_top
% 3.90/0.96      | v2_pre_topc(X0) != iProver_top
% 3.90/0.96      | v2_pre_topc(X3) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1994,plain,
% 3.90/0.96      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.90/0.96      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.90/0.96      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,X2) != iProver_top
% 3.90/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(X2) = iProver_top
% 3.90/0.96      | v2_struct_0(sK1) = iProver_top
% 3.90/0.96      | l1_pre_topc(X2) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X2) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK1) != iProver_top ),
% 3.90/0.96      inference(equality_resolution,[status(thm)],[c_1394]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_35,negated_conjecture,
% 3.90/0.96      ( ~ v2_struct_0(sK1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f75]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_42,plain,
% 3.90/0.96      ( v2_struct_0(sK1) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_34,negated_conjecture,
% 3.90/0.96      ( v2_pre_topc(sK1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_43,plain,
% 3.90/0.96      ( v2_pre_topc(sK1) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_33,negated_conjecture,
% 3.90/0.96      ( l1_pre_topc(sK1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_44,plain,
% 3.90/0.96      ( l1_pre_topc(sK1) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3713,plain,
% 3.90/0.96      ( v2_pre_topc(X2) != iProver_top
% 3.90/0.96      | v2_struct_0(X2) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,X2) != iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
% 3.90/0.96      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.90/0.96      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.90/0.96      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.90/0.96      | l1_pre_topc(X2) != iProver_top ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_1994,c_42,c_43,c_44]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3714,plain,
% 3.90/0.96      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.90/0.96      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.90/0.96      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,X2) != iProver_top
% 3.90/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(X2) = iProver_top
% 3.90/0.96      | l1_pre_topc(X2) != iProver_top
% 3.90/0.96      | v2_pre_topc(X2) != iProver_top ),
% 3.90/0.96      inference(renaming,[status(thm)],[c_3713]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1401,plain,
% 3.90/0.96      ( l1_pre_topc(sK1) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2030,plain,
% 3.90/0.96      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_1401,c_1395]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3717,plain,
% 3.90/0.96      ( u1_struct_0(X0) != k2_struct_0(sK3)
% 3.90/0.96      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.90/0.96      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,X2) != iProver_top
% 3.90/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(X2) = iProver_top
% 3.90/0.96      | l1_pre_topc(X2) != iProver_top
% 3.90/0.96      | v2_pre_topc(X2) != iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_3714,c_2030,c_2264]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3722,plain,
% 3.90/0.96      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.90/0.96      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK3,X1) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(sK3) = iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_2264,c_3717]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3727,plain,
% 3.90/0.96      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.90/0.96      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK3,X1) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(sK3) = iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_3722,c_2264]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_30,negated_conjecture,
% 3.90/0.96      ( ~ v2_struct_0(sK3) ),
% 3.90/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_47,plain,
% 3.90/0.96      ( v2_struct_0(sK3) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_26,negated_conjecture,
% 3.90/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.90/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1406,plain,
% 3.90/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2184,plain,
% 3.90/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.90/0.96      inference(demodulation,[status(thm)],[c_2030,c_1406]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2293,plain,
% 3.90/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_2184,c_2264]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_11732,plain,
% 3.90/0.96      ( v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.90/0.96      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK3,X1) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_3727,c_47,c_2293]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_11733,plain,
% 3.90/0.96      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.90/0.96      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK3,X1) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.90/0.96      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.90/0.96      inference(renaming,[status(thm)],[c_11732]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_11738,plain,
% 3.90/0.96      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.90/0.96      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.90/0.96      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 3.90/0.96      | v2_struct_0(sK0) = iProver_top
% 3.90/0.96      | v2_struct_0(sK2) = iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK0) != iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_1425,c_11733]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_31,negated_conjecture,
% 3.90/0.96      ( m1_pre_topc(sK2,sK0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1403,plain,
% 3.90/0.96      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2055,plain,
% 3.90/0.96      ( l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK2) = iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_1403,c_1420]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_46,plain,
% 3.90/0.96      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1589,plain,
% 3.90/0.96      ( ~ m1_pre_topc(sK2,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK2) ),
% 3.90/0.96      inference(instantiation,[status(thm)],[c_5]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1713,plain,
% 3.90/0.96      ( ~ m1_pre_topc(sK2,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.90/0.96      inference(instantiation,[status(thm)],[c_1589]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1714,plain,
% 3.90/0.96      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK2) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_1713]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2266,plain,
% 3.90/0.96      ( l1_pre_topc(sK2) = iProver_top ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_2055,c_41,c_46,c_1714]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2270,plain,
% 3.90/0.96      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_2266,c_1395]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_11740,plain,
% 3.90/0.96      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.90/0.96      | v3_pre_topc(k2_struct_0(sK2),sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.90/0.96      | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
% 3.90/0.96      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 3.90/0.96      | v2_struct_0(sK0) = iProver_top
% 3.90/0.96      | v2_struct_0(sK2) = iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK0) != iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_11738,c_2270]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_16,plain,
% 3.90/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1)
% 3.90/0.96      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f68]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1412,plain,
% 3.90/0.96      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 3.90/0.96      | m1_pre_topc(X0,X1) != iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2700,plain,
% 3.90/0.96      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 3.90/0.96      | v2_struct_0(sK0) = iProver_top
% 3.90/0.96      | v2_struct_0(sK2) = iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK0) != iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_1403,c_1412]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_25,negated_conjecture,
% 3.90/0.96      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.90/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2340,plain,
% 3.90/0.96      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.90/0.96      inference(demodulation,[status(thm)],[c_2270,c_25]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2701,plain,
% 3.90/0.96      ( k1_tsep_1(sK0,sK2,sK2) = sK3
% 3.90/0.96      | v2_struct_0(sK0) = iProver_top
% 3.90/0.96      | v2_struct_0(sK2) = iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK0) != iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_2700,c_2270,c_2340]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_38,negated_conjecture,
% 3.90/0.96      ( ~ v2_struct_0(sK0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f72]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_39,plain,
% 3.90/0.96      ( v2_struct_0(sK0) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_37,negated_conjecture,
% 3.90/0.96      ( v2_pre_topc(sK0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f73]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_40,plain,
% 3.90/0.96      ( v2_pre_topc(sK0) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_32,negated_conjecture,
% 3.90/0.96      ( ~ v2_struct_0(sK2) ),
% 3.90/0.96      inference(cnf_transformation,[],[f78]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_45,plain,
% 3.90/0.96      ( v2_struct_0(sK2) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2973,plain,
% 3.90/0.96      ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_2701,c_39,c_40,c_41,c_45]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_15,plain,
% 3.90/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.90/0.96      | ~ m1_pre_topc(X2,X1)
% 3.90/0.96      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 3.90/0.96      | v2_struct_0(X1)
% 3.90/0.96      | v2_struct_0(X0)
% 3.90/0.96      | v2_struct_0(X2)
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1413,plain,
% 3.90/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 3.90/0.96      | m1_pre_topc(X2,X1) != iProver_top
% 3.90/0.96      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
% 3.90/0.96      | v2_struct_0(X1) = iProver_top
% 3.90/0.96      | v2_struct_0(X0) = iProver_top
% 3.90/0.96      | v2_struct_0(X2) = iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3028,plain,
% 3.90/0.96      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.90/0.96      | m1_pre_topc(sK2,sK3) = iProver_top
% 3.90/0.96      | v2_struct_0(sK0) = iProver_top
% 3.90/0.96      | v2_struct_0(sK2) = iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK0) != iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_2973,c_1413]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_10,plain,
% 3.90/0.96      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.90/0.96      | ~ l1_pre_topc(X0)
% 3.90/0.96      | ~ v2_pre_topc(X0) ),
% 3.90/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1415,plain,
% 3.90/0.96      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 3.90/0.96      | l1_pre_topc(X0) != iProver_top
% 3.90/0.96      | v2_pre_topc(X0) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1,plain,
% 3.90/0.96      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.90/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1422,plain,
% 3.90/0.96      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_0,plain,
% 3.90/0.96      ( k2_subset_1(X0) = X0 ),
% 3.90/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1424,plain,
% 3.90/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_1422,c_0]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_9,plain,
% 3.90/0.96      ( ~ v3_pre_topc(X0,X1)
% 3.90/0.96      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.90/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/0.96      | ~ l1_pre_topc(X1)
% 3.90/0.96      | ~ v2_pre_topc(X1) ),
% 3.90/0.96      inference(cnf_transformation,[],[f58]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1416,plain,
% 3.90/0.96      ( v3_pre_topc(X0,X1) != iProver_top
% 3.90/0.96      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.90/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.90/0.96      | l1_pre_topc(X1) != iProver_top
% 3.90/0.96      | v2_pre_topc(X1) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2488,plain,
% 3.90/0.96      ( v3_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.90/0.96      | v3_pre_topc(X0,sK2) != iProver_top
% 3.90/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK2) != iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_2270,c_1416]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2495,plain,
% 3.90/0.96      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.90/0.96      | v3_pre_topc(X0,sK3) = iProver_top
% 3.90/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK2) != iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_2488,c_2270,c_2340]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1871,plain,
% 3.90/0.96      ( ~ m1_pre_topc(sK2,X0)
% 3.90/0.96      | ~ l1_pre_topc(X0)
% 3.90/0.96      | ~ v2_pre_topc(X0)
% 3.90/0.96      | v2_pre_topc(sK2) ),
% 3.90/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2069,plain,
% 3.90/0.96      ( ~ m1_pre_topc(sK2,sK0)
% 3.90/0.96      | ~ l1_pre_topc(sK0)
% 3.90/0.96      | ~ v2_pre_topc(sK0)
% 3.90/0.96      | v2_pre_topc(sK2) ),
% 3.90/0.96      inference(instantiation,[status(thm)],[c_1871]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2070,plain,
% 3.90/0.96      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.90/0.96      | l1_pre_topc(sK0) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK0) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK2) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_2069]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2964,plain,
% 3.90/0.96      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.90/0.96      | v3_pre_topc(X0,sK3) = iProver_top
% 3.90/0.96      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 3.90/0.96      inference(global_propositional_subsumption,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_2495,c_40,c_41,c_46,c_1714,c_2070]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2970,plain,
% 3.90/0.96      ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 3.90/0.96      | v3_pre_topc(k2_struct_0(sK2),sK3) = iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_1424,c_2964]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_3025,plain,
% 3.90/0.96      ( v3_pre_topc(k2_struct_0(sK2),sK3) = iProver_top
% 3.90/0.96      | l1_pre_topc(sK2) != iProver_top
% 3.90/0.96      | v2_pre_topc(sK2) != iProver_top ),
% 3.90/0.96      inference(superposition,[status(thm)],[c_1415,c_2970]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_23,negated_conjecture,
% 3.90/0.96      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.90/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1408,plain,
% 3.90/0.96      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1423,plain,
% 3.90/0.96      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.90/0.96      inference(light_normalisation,[status(thm)],[c_1408,c_22]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2339,plain,
% 3.90/0.96      ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
% 3.90/0.96      inference(demodulation,[status(thm)],[c_2270,c_1423]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_24,negated_conjecture,
% 3.90/0.96      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.90/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_1407,plain,
% 3.90/0.96      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_2295,plain,
% 3.90/0.96      ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.90/0.96      inference(demodulation,[status(thm)],[c_2264,c_1407]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_20,negated_conjecture,
% 3.90/0.96      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.90/0.96      inference(cnf_transformation,[],[f90]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(c_55,plain,
% 3.90/0.96      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.90/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.90/0.96  
% 3.90/0.96  cnf(contradiction,plain,
% 3.90/0.96      ( $false ),
% 3.90/0.96      inference(minisat,
% 3.90/0.96                [status(thm)],
% 3.90/0.96                [c_11740,c_3028,c_3025,c_2339,c_2295,c_2070,c_1714,c_55,
% 3.90/0.96                 c_48,c_46,c_45,c_41,c_40,c_39]) ).
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/0.96  
% 3.90/0.96  ------                               Statistics
% 3.90/0.96  
% 3.90/0.96  ------ General
% 3.90/0.96  
% 3.90/0.96  abstr_ref_over_cycles:                  0
% 3.90/0.96  abstr_ref_under_cycles:                 0
% 3.90/0.96  gc_basic_clause_elim:                   0
% 3.90/0.96  forced_gc_time:                         0
% 3.90/0.96  parsing_time:                           0.01
% 3.90/0.96  unif_index_cands_time:                  0.
% 3.90/0.96  unif_index_add_time:                    0.
% 3.90/0.96  orderings_time:                         0.
% 3.90/0.96  out_proof_time:                         0.013
% 3.90/0.96  total_time:                             0.499
% 3.90/0.96  num_of_symbols:                         58
% 3.90/0.96  num_of_terms:                           10080
% 3.90/0.96  
% 3.90/0.96  ------ Preprocessing
% 3.90/0.96  
% 3.90/0.96  num_of_splits:                          0
% 3.90/0.96  num_of_split_atoms:                     0
% 3.90/0.96  num_of_reused_defs:                     0
% 3.90/0.96  num_eq_ax_congr_red:                    18
% 3.90/0.96  num_of_sem_filtered_clauses:            1
% 3.90/0.96  num_of_subtypes:                        0
% 3.90/0.96  monotx_restored_types:                  0
% 3.90/0.96  sat_num_of_epr_types:                   0
% 3.90/0.96  sat_num_of_non_cyclic_types:            0
% 3.90/0.96  sat_guarded_non_collapsed_types:        0
% 3.90/0.96  num_pure_diseq_elim:                    0
% 3.90/0.96  simp_replaced_by:                       0
% 3.90/0.96  res_preprocessed:                       168
% 3.90/0.96  prep_upred:                             0
% 3.90/0.96  prep_unflattend:                        6
% 3.90/0.96  smt_new_axioms:                         0
% 3.90/0.96  pred_elim_cands:                        7
% 3.90/0.96  pred_elim:                              4
% 3.90/0.96  pred_elim_cl:                           5
% 3.90/0.96  pred_elim_cycles:                       6
% 3.90/0.96  merged_defs:                            0
% 3.90/0.96  merged_defs_ncl:                        0
% 3.90/0.96  bin_hyper_res:                          0
% 3.90/0.96  prep_cycles:                            4
% 3.90/0.96  pred_elim_time:                         0.008
% 3.90/0.96  splitting_time:                         0.
% 3.90/0.96  sem_filter_time:                        0.
% 3.90/0.96  monotx_time:                            0.
% 3.90/0.96  subtype_inf_time:                       0.
% 3.90/0.96  
% 3.90/0.96  ------ Problem properties
% 3.90/0.96  
% 3.90/0.96  clauses:                                33
% 3.90/0.96  conjectures:                            17
% 3.90/0.96  epr:                                    15
% 3.90/0.96  horn:                                   29
% 3.90/0.96  ground:                                 17
% 3.90/0.96  unary:                                  19
% 3.90/0.96  binary:                                 1
% 3.90/0.96  lits:                                   109
% 3.90/0.96  lits_eq:                                9
% 3.90/0.96  fd_pure:                                0
% 3.90/0.96  fd_pseudo:                              0
% 3.90/0.96  fd_cond:                                0
% 3.90/0.96  fd_pseudo_cond:                         0
% 3.90/0.96  ac_symbols:                             0
% 3.90/0.96  
% 3.90/0.96  ------ Propositional Solver
% 3.90/0.96  
% 3.90/0.96  prop_solver_calls:                      33
% 3.90/0.96  prop_fast_solver_calls:                 3405
% 3.90/0.96  smt_solver_calls:                       0
% 3.90/0.96  smt_fast_solver_calls:                  0
% 3.90/0.96  prop_num_of_clauses:                    5991
% 3.90/0.96  prop_preprocess_simplified:             11233
% 3.90/0.96  prop_fo_subsumed:                       153
% 3.90/0.96  prop_solver_time:                       0.
% 3.90/0.96  smt_solver_time:                        0.
% 3.90/0.96  smt_fast_solver_time:                   0.
% 3.90/0.96  prop_fast_solver_time:                  0.
% 3.90/0.96  prop_unsat_core_time:                   0.001
% 3.90/0.96  
% 3.90/0.96  ------ QBF
% 3.90/0.96  
% 3.90/0.96  qbf_q_res:                              0
% 3.90/0.96  qbf_num_tautologies:                    0
% 3.90/0.96  qbf_prep_cycles:                        0
% 3.90/0.96  
% 3.90/0.96  ------ BMC1
% 3.90/0.96  
% 3.90/0.96  bmc1_current_bound:                     -1
% 3.90/0.96  bmc1_last_solved_bound:                 -1
% 3.90/0.96  bmc1_unsat_core_size:                   -1
% 3.90/0.96  bmc1_unsat_core_parents_size:           -1
% 3.90/0.96  bmc1_merge_next_fun:                    0
% 3.90/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.90/0.96  
% 3.90/0.96  ------ Instantiation
% 3.90/0.96  
% 3.90/0.96  inst_num_of_clauses:                    1719
% 3.90/0.96  inst_num_in_passive:                    487
% 3.90/0.96  inst_num_in_active:                     897
% 3.90/0.96  inst_num_in_unprocessed:                335
% 3.90/0.96  inst_num_of_loops:                      1010
% 3.90/0.96  inst_num_of_learning_restarts:          0
% 3.90/0.96  inst_num_moves_active_passive:          107
% 3.90/0.96  inst_lit_activity:                      0
% 3.90/0.96  inst_lit_activity_moves:                0
% 3.90/0.96  inst_num_tautologies:                   0
% 3.90/0.96  inst_num_prop_implied:                  0
% 3.90/0.96  inst_num_existing_simplified:           0
% 3.90/0.96  inst_num_eq_res_simplified:             0
% 3.90/0.96  inst_num_child_elim:                    0
% 3.90/0.96  inst_num_of_dismatching_blockings:      51
% 3.90/0.96  inst_num_of_non_proper_insts:           1680
% 3.90/0.96  inst_num_of_duplicates:                 0
% 3.90/0.96  inst_inst_num_from_inst_to_res:         0
% 3.90/0.96  inst_dismatching_checking_time:         0.
% 3.90/0.96  
% 3.90/0.96  ------ Resolution
% 3.90/0.96  
% 3.90/0.96  res_num_of_clauses:                     0
% 3.90/0.96  res_num_in_passive:                     0
% 3.90/0.96  res_num_in_active:                      0
% 3.90/0.96  res_num_of_loops:                       172
% 3.90/0.96  res_forward_subset_subsumed:            193
% 3.90/0.96  res_backward_subset_subsumed:           4
% 3.90/0.96  res_forward_subsumed:                   0
% 3.90/0.96  res_backward_subsumed:                  0
% 3.90/0.96  res_forward_subsumption_resolution:     6
% 3.90/0.96  res_backward_subsumption_resolution:    0
% 3.90/0.96  res_clause_to_clause_subsumption:       2687
% 3.90/0.96  res_orphan_elimination:                 0
% 3.90/0.96  res_tautology_del:                      157
% 3.90/0.96  res_num_eq_res_simplified:              0
% 3.90/0.96  res_num_sel_changes:                    0
% 3.90/0.96  res_moves_from_active_to_pass:          0
% 3.90/0.96  
% 3.90/0.96  ------ Superposition
% 3.90/0.96  
% 3.90/0.96  sup_time_total:                         0.
% 3.90/0.96  sup_time_generating:                    0.
% 3.90/0.96  sup_time_sim_full:                      0.
% 3.90/0.96  sup_time_sim_immed:                     0.
% 3.90/0.96  
% 3.90/0.96  sup_num_of_clauses:                     336
% 3.90/0.96  sup_num_in_active:                      182
% 3.90/0.96  sup_num_in_passive:                     154
% 3.90/0.96  sup_num_of_loops:                       200
% 3.90/0.96  sup_fw_superposition:                   384
% 3.90/0.96  sup_bw_superposition:                   236
% 3.90/0.96  sup_immediate_simplified:               344
% 3.90/0.96  sup_given_eliminated:                   0
% 3.90/0.96  comparisons_done:                       0
% 3.90/0.96  comparisons_avoided:                    0
% 3.90/0.96  
% 3.90/0.96  ------ Simplifications
% 3.90/0.96  
% 3.90/0.96  
% 3.90/0.96  sim_fw_subset_subsumed:                 49
% 3.90/0.96  sim_bw_subset_subsumed:                 15
% 3.90/0.96  sim_fw_subsumed:                        149
% 3.90/0.96  sim_bw_subsumed:                        18
% 3.90/0.96  sim_fw_subsumption_res:                 0
% 3.90/0.96  sim_bw_subsumption_res:                 0
% 3.90/0.96  sim_tautology_del:                      30
% 3.90/0.96  sim_eq_tautology_del:                   2
% 3.90/0.96  sim_eq_res_simp:                        0
% 3.90/0.96  sim_fw_demodulated:                     0
% 3.90/0.96  sim_bw_demodulated:                     8
% 3.90/0.96  sim_light_normalised:                   186
% 3.90/0.96  sim_joinable_taut:                      0
% 3.90/0.96  sim_joinable_simp:                      0
% 3.90/0.96  sim_ac_normalised:                      0
% 3.90/0.96  sim_smt_subsumption:                    0
% 3.90/0.96  
%------------------------------------------------------------------------------
