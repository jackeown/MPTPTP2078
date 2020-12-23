%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:38 EST 2020

% Result     : Theorem 27.42s
% Output     : CNFRefutation 27.42s
% Verified   : 
% Statistics : Number of formulae       :  231 (1936 expanded)
%              Number of clauses        :  145 ( 551 expanded)
%              Number of leaves         :   24 ( 772 expanded)
%              Depth                    :   26
%              Number of atoms          : 1360 (24072 expanded)
%              Number of equality atoms :  351 (3707 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f68,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f36])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f37,f50,f49,f48,f47,f46,f45,f44])).

fof(f79,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X0,X4,X5)
                                  | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X5)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_871,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1461,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_860,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1470,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_876,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1456,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_2378,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1456])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2694,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2378,c_41])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_406,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_849,plain,
    ( ~ l1_pre_topc(X0_54)
    | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_1481,plain,
    ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_3188,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2694,c_1481])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_230,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_3])).

cnf(c_231,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_850,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_231])).

cnf(c_1480,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_5894,plain,
    ( m1_pre_topc(X0_54,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_1480])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_864,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3849,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3188,c_864])).

cnf(c_5978,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X0_54,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5894,c_3849])).

cnf(c_6054,plain,
    ( m1_pre_topc(X0_54,sK3) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5978,c_41,c_2378])).

cnf(c_6055,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X0_54,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6054])).

cnf(c_6063,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_6055])).

cnf(c_6105,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6063,c_41,c_2378])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_449,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_453,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_28])).

cnf(c_454,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_485,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_454,c_17])).

cnf(c_847,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_pre_topc(X3_54,X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4,u1_struct_0(X3_54)) = k3_tmap_1(X2_54,X1_54,X0_54,X3_54,sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(X0_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_485])).

cnf(c_1483,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_2369,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1483])).

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

cnf(c_2937,plain,
    ( v2_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4)
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2369,c_42,c_43,c_44])).

cnf(c_2938,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_2937])).

cnf(c_2949,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2938])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9847,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2949,c_51])).

cnf(c_858,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1472,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_3185,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1472,c_1481])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_862,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1468,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_2377,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1456])).

cnf(c_2688,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_41])).

cnf(c_3187,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2688,c_1481])).

cnf(c_9853,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9847,c_3185,c_3187])).

cnf(c_9868,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_54,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6105,c_9853])).

cnf(c_9921,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(X0_54,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9868,c_3188])).

cnf(c_123073,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_9921])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_877,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1455,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_1883,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1455])).

cnf(c_123477,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_123073,c_40,c_41,c_47,c_1883,c_2377])).

cnf(c_123068,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_9921])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_123469,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_123068,c_39,c_40,c_41])).

cnf(c_123480,plain,
    ( k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_123477,c_123469])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_868,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1464,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_22,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_867,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1527,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1464,c_867])).

cnf(c_127332,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_123480,c_1527])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_568,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_569,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_573,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X2)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_28])).

cnf(c_574,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
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
    inference(renaming,[status(thm)],[c_573])).

cnf(c_617,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
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
    inference(forward_subsumption_resolution,[status(thm)],[c_574,c_17])).

cnf(c_845,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
    | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
    | ~ v1_tsep_1(X0_54,X2_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X0_54,X3_54)
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
    inference(subtyping,[status(esa)],[c_617])).

cnf(c_1822,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,sK3,X0_54,sK4),X0_55)
    | r1_tmap_1(sK3,X1_54,sK4,X0_55)
    | ~ v1_tsep_1(X0_54,X2_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X0_54,sK3)
    | ~ m1_pre_topc(sK3,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_11020,plain,
    ( ~ r1_tmap_1(sK2,X0_54,k3_tmap_1(X1_54,X0_54,sK3,sK2,sK4),X0_55)
    | r1_tmap_1(sK3,X0_54,sK4,X0_55)
    | ~ v1_tsep_1(sK2,X1_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_20803,plain,
    ( ~ r1_tmap_1(sK2,X0_54,k3_tmap_1(sK3,X0_54,sK3,sK2,sK4),X0_55)
    | r1_tmap_1(sK3,X0_54,sK4,X0_55)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_11020])).

cnf(c_47272,plain,
    ( ~ r1_tmap_1(sK2,X0_54,k3_tmap_1(sK3,X0_54,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,X0_54,sK4,sK5)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_20803])).

cnf(c_47273,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK2,X0_54,k3_tmap_1(sK3,X0_54,sK3,sK2,sK4),sK5) != iProver_top
    | r1_tmap_1(sK3,X0_54,sK4,sK5) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47272])).

cnf(c_47275,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK2,sK4),sK5) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47273])).

cnf(c_9,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_873,plain,
    ( v1_tsep_1(X0_54,X1_54)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1459,plain,
    ( v1_tsep_1(X0_54,X1_54) = iProver_top
    | v1_tsep_1(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_1638,plain,
    ( v1_tsep_1(X0_54,X1_54) = iProver_top
    | v1_tsep_1(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1459,c_1455,c_1456])).

cnf(c_9102,plain,
    ( v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X0_54) != iProver_top
    | v1_tsep_1(sK2,X0_54) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_1638])).

cnf(c_9158,plain,
    ( v1_tsep_1(sK2,X0_54) = iProver_top
    | v1_tsep_1(sK3,X0_54) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9102,c_3188,c_3849])).

cnf(c_1887,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1455])).

cnf(c_9362,plain,
    ( v2_pre_topc(X0_54) != iProver_top
    | v1_tsep_1(sK2,X0_54) = iProver_top
    | v1_tsep_1(sK3,X0_54) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9158,c_40,c_41,c_1887,c_2378])).

cnf(c_9363,plain,
    ( v1_tsep_1(sK2,X0_54) = iProver_top
    | v1_tsep_1(sK3,X0_54) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_9362])).

cnf(c_9375,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | v1_tsep_1(sK3,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_9363])).

cnf(c_6,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_15,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_209,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_15])).

cnf(c_421,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X1 != X2
    | u1_struct_0(X0) != k2_struct_0(X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_209])).

cnf(c_422,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_848,plain,
    ( v1_tsep_1(X0_54,X1_54)
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | u1_struct_0(X0_54) != k2_struct_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_3767,plain,
    ( v1_tsep_1(sK3,X0_54)
    | ~ m1_pre_topc(sK3,X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54)
    | u1_struct_0(sK3) != k2_struct_0(X0_54) ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_5569,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3767])).

cnf(c_5570,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | v1_tsep_1(sK3,sK3) = iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5569])).

cnf(c_1977,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_1982,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_1948,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_1950,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_880,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1820,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_866,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1465,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_1508,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1465,c_867])).

cnf(c_879,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_913,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_887,plain,
    ( u1_struct_0(X0_54) = u1_struct_0(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_901,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_55,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_127332,c_47275,c_9375,c_6063,c_5570,c_2378,c_2377,c_1982,c_1950,c_1883,c_1820,c_1508,c_913,c_901,c_55,c_52,c_51,c_47,c_45,c_44,c_43,c_42,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.42/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.42/4.01  
% 27.42/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.42/4.01  
% 27.42/4.01  ------  iProver source info
% 27.42/4.01  
% 27.42/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.42/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.42/4.01  git: non_committed_changes: false
% 27.42/4.01  git: last_make_outside_of_git: false
% 27.42/4.01  
% 27.42/4.01  ------ 
% 27.42/4.01  
% 27.42/4.01  ------ Input Options
% 27.42/4.01  
% 27.42/4.01  --out_options                           all
% 27.42/4.01  --tptp_safe_out                         true
% 27.42/4.01  --problem_path                          ""
% 27.42/4.01  --include_path                          ""
% 27.42/4.01  --clausifier                            res/vclausify_rel
% 27.42/4.01  --clausifier_options                    --mode clausify
% 27.42/4.01  --stdin                                 false
% 27.42/4.01  --stats_out                             all
% 27.42/4.01  
% 27.42/4.01  ------ General Options
% 27.42/4.01  
% 27.42/4.01  --fof                                   false
% 27.42/4.01  --time_out_real                         305.
% 27.42/4.01  --time_out_virtual                      -1.
% 27.42/4.01  --symbol_type_check                     false
% 27.42/4.01  --clausify_out                          false
% 27.42/4.01  --sig_cnt_out                           false
% 27.42/4.01  --trig_cnt_out                          false
% 27.42/4.01  --trig_cnt_out_tolerance                1.
% 27.42/4.01  --trig_cnt_out_sk_spl                   false
% 27.42/4.01  --abstr_cl_out                          false
% 27.42/4.01  
% 27.42/4.01  ------ Global Options
% 27.42/4.01  
% 27.42/4.01  --schedule                              default
% 27.42/4.01  --add_important_lit                     false
% 27.42/4.01  --prop_solver_per_cl                    1000
% 27.42/4.01  --min_unsat_core                        false
% 27.42/4.01  --soft_assumptions                      false
% 27.42/4.01  --soft_lemma_size                       3
% 27.42/4.01  --prop_impl_unit_size                   0
% 27.42/4.01  --prop_impl_unit                        []
% 27.42/4.01  --share_sel_clauses                     true
% 27.42/4.01  --reset_solvers                         false
% 27.42/4.01  --bc_imp_inh                            [conj_cone]
% 27.42/4.01  --conj_cone_tolerance                   3.
% 27.42/4.01  --extra_neg_conj                        none
% 27.42/4.01  --large_theory_mode                     true
% 27.42/4.01  --prolific_symb_bound                   200
% 27.42/4.01  --lt_threshold                          2000
% 27.42/4.01  --clause_weak_htbl                      true
% 27.42/4.01  --gc_record_bc_elim                     false
% 27.42/4.01  
% 27.42/4.01  ------ Preprocessing Options
% 27.42/4.01  
% 27.42/4.01  --preprocessing_flag                    true
% 27.42/4.01  --time_out_prep_mult                    0.1
% 27.42/4.01  --splitting_mode                        input
% 27.42/4.01  --splitting_grd                         true
% 27.42/4.01  --splitting_cvd                         false
% 27.42/4.01  --splitting_cvd_svl                     false
% 27.42/4.01  --splitting_nvd                         32
% 27.42/4.01  --sub_typing                            true
% 27.42/4.01  --prep_gs_sim                           true
% 27.42/4.01  --prep_unflatten                        true
% 27.42/4.01  --prep_res_sim                          true
% 27.42/4.01  --prep_upred                            true
% 27.42/4.01  --prep_sem_filter                       exhaustive
% 27.42/4.01  --prep_sem_filter_out                   false
% 27.42/4.01  --pred_elim                             true
% 27.42/4.01  --res_sim_input                         true
% 27.42/4.01  --eq_ax_congr_red                       true
% 27.42/4.01  --pure_diseq_elim                       true
% 27.42/4.01  --brand_transform                       false
% 27.42/4.01  --non_eq_to_eq                          false
% 27.42/4.01  --prep_def_merge                        true
% 27.42/4.01  --prep_def_merge_prop_impl              false
% 27.42/4.01  --prep_def_merge_mbd                    true
% 27.42/4.01  --prep_def_merge_tr_red                 false
% 27.42/4.01  --prep_def_merge_tr_cl                  false
% 27.42/4.01  --smt_preprocessing                     true
% 27.42/4.01  --smt_ac_axioms                         fast
% 27.42/4.01  --preprocessed_out                      false
% 27.42/4.01  --preprocessed_stats                    false
% 27.42/4.01  
% 27.42/4.01  ------ Abstraction refinement Options
% 27.42/4.01  
% 27.42/4.01  --abstr_ref                             []
% 27.42/4.01  --abstr_ref_prep                        false
% 27.42/4.01  --abstr_ref_until_sat                   false
% 27.42/4.01  --abstr_ref_sig_restrict                funpre
% 27.42/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.42/4.01  --abstr_ref_under                       []
% 27.42/4.01  
% 27.42/4.01  ------ SAT Options
% 27.42/4.01  
% 27.42/4.01  --sat_mode                              false
% 27.42/4.01  --sat_fm_restart_options                ""
% 27.42/4.01  --sat_gr_def                            false
% 27.42/4.01  --sat_epr_types                         true
% 27.42/4.01  --sat_non_cyclic_types                  false
% 27.42/4.01  --sat_finite_models                     false
% 27.42/4.01  --sat_fm_lemmas                         false
% 27.42/4.01  --sat_fm_prep                           false
% 27.42/4.01  --sat_fm_uc_incr                        true
% 27.42/4.01  --sat_out_model                         small
% 27.42/4.01  --sat_out_clauses                       false
% 27.42/4.01  
% 27.42/4.01  ------ QBF Options
% 27.42/4.01  
% 27.42/4.01  --qbf_mode                              false
% 27.42/4.01  --qbf_elim_univ                         false
% 27.42/4.01  --qbf_dom_inst                          none
% 27.42/4.01  --qbf_dom_pre_inst                      false
% 27.42/4.01  --qbf_sk_in                             false
% 27.42/4.01  --qbf_pred_elim                         true
% 27.42/4.01  --qbf_split                             512
% 27.42/4.01  
% 27.42/4.01  ------ BMC1 Options
% 27.42/4.01  
% 27.42/4.01  --bmc1_incremental                      false
% 27.42/4.01  --bmc1_axioms                           reachable_all
% 27.42/4.01  --bmc1_min_bound                        0
% 27.42/4.01  --bmc1_max_bound                        -1
% 27.42/4.01  --bmc1_max_bound_default                -1
% 27.42/4.01  --bmc1_symbol_reachability              true
% 27.42/4.01  --bmc1_property_lemmas                  false
% 27.42/4.01  --bmc1_k_induction                      false
% 27.42/4.01  --bmc1_non_equiv_states                 false
% 27.42/4.01  --bmc1_deadlock                         false
% 27.42/4.01  --bmc1_ucm                              false
% 27.42/4.01  --bmc1_add_unsat_core                   none
% 27.42/4.01  --bmc1_unsat_core_children              false
% 27.42/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.42/4.01  --bmc1_out_stat                         full
% 27.42/4.01  --bmc1_ground_init                      false
% 27.42/4.01  --bmc1_pre_inst_next_state              false
% 27.42/4.01  --bmc1_pre_inst_state                   false
% 27.42/4.01  --bmc1_pre_inst_reach_state             false
% 27.42/4.01  --bmc1_out_unsat_core                   false
% 27.42/4.01  --bmc1_aig_witness_out                  false
% 27.42/4.01  --bmc1_verbose                          false
% 27.42/4.01  --bmc1_dump_clauses_tptp                false
% 27.42/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.42/4.01  --bmc1_dump_file                        -
% 27.42/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.42/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.42/4.01  --bmc1_ucm_extend_mode                  1
% 27.42/4.01  --bmc1_ucm_init_mode                    2
% 27.42/4.01  --bmc1_ucm_cone_mode                    none
% 27.42/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.42/4.01  --bmc1_ucm_relax_model                  4
% 27.42/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.42/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.42/4.01  --bmc1_ucm_layered_model                none
% 27.42/4.01  --bmc1_ucm_max_lemma_size               10
% 27.42/4.01  
% 27.42/4.01  ------ AIG Options
% 27.42/4.01  
% 27.42/4.01  --aig_mode                              false
% 27.42/4.01  
% 27.42/4.01  ------ Instantiation Options
% 27.42/4.01  
% 27.42/4.01  --instantiation_flag                    true
% 27.42/4.01  --inst_sos_flag                         false
% 27.42/4.01  --inst_sos_phase                        true
% 27.42/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.42/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.42/4.01  --inst_lit_sel_side                     num_symb
% 27.42/4.01  --inst_solver_per_active                1400
% 27.42/4.01  --inst_solver_calls_frac                1.
% 27.42/4.01  --inst_passive_queue_type               priority_queues
% 27.42/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.42/4.01  --inst_passive_queues_freq              [25;2]
% 27.42/4.01  --inst_dismatching                      true
% 27.42/4.01  --inst_eager_unprocessed_to_passive     true
% 27.42/4.01  --inst_prop_sim_given                   true
% 27.42/4.01  --inst_prop_sim_new                     false
% 27.42/4.01  --inst_subs_new                         false
% 27.42/4.01  --inst_eq_res_simp                      false
% 27.42/4.01  --inst_subs_given                       false
% 27.42/4.01  --inst_orphan_elimination               true
% 27.42/4.01  --inst_learning_loop_flag               true
% 27.42/4.01  --inst_learning_start                   3000
% 27.42/4.01  --inst_learning_factor                  2
% 27.42/4.01  --inst_start_prop_sim_after_learn       3
% 27.42/4.01  --inst_sel_renew                        solver
% 27.42/4.01  --inst_lit_activity_flag                true
% 27.42/4.01  --inst_restr_to_given                   false
% 27.42/4.01  --inst_activity_threshold               500
% 27.42/4.01  --inst_out_proof                        true
% 27.42/4.01  
% 27.42/4.01  ------ Resolution Options
% 27.42/4.01  
% 27.42/4.01  --resolution_flag                       true
% 27.42/4.01  --res_lit_sel                           adaptive
% 27.42/4.01  --res_lit_sel_side                      none
% 27.42/4.01  --res_ordering                          kbo
% 27.42/4.01  --res_to_prop_solver                    active
% 27.42/4.01  --res_prop_simpl_new                    false
% 27.42/4.01  --res_prop_simpl_given                  true
% 27.42/4.01  --res_passive_queue_type                priority_queues
% 27.42/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.42/4.01  --res_passive_queues_freq               [15;5]
% 27.42/4.01  --res_forward_subs                      full
% 27.42/4.01  --res_backward_subs                     full
% 27.42/4.01  --res_forward_subs_resolution           true
% 27.42/4.01  --res_backward_subs_resolution          true
% 27.42/4.01  --res_orphan_elimination                true
% 27.42/4.01  --res_time_limit                        2.
% 27.42/4.01  --res_out_proof                         true
% 27.42/4.01  
% 27.42/4.01  ------ Superposition Options
% 27.42/4.01  
% 27.42/4.01  --superposition_flag                    true
% 27.42/4.01  --sup_passive_queue_type                priority_queues
% 27.42/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.42/4.01  --sup_passive_queues_freq               [8;1;4]
% 27.42/4.01  --demod_completeness_check              fast
% 27.42/4.01  --demod_use_ground                      true
% 27.42/4.01  --sup_to_prop_solver                    passive
% 27.42/4.01  --sup_prop_simpl_new                    true
% 27.42/4.01  --sup_prop_simpl_given                  true
% 27.42/4.01  --sup_fun_splitting                     false
% 27.42/4.01  --sup_smt_interval                      50000
% 27.42/4.01  
% 27.42/4.01  ------ Superposition Simplification Setup
% 27.42/4.01  
% 27.42/4.01  --sup_indices_passive                   []
% 27.42/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.42/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.01  --sup_full_bw                           [BwDemod]
% 27.42/4.01  --sup_immed_triv                        [TrivRules]
% 27.42/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.01  --sup_immed_bw_main                     []
% 27.42/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.42/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.01  
% 27.42/4.01  ------ Combination Options
% 27.42/4.01  
% 27.42/4.01  --comb_res_mult                         3
% 27.42/4.01  --comb_sup_mult                         2
% 27.42/4.01  --comb_inst_mult                        10
% 27.42/4.01  
% 27.42/4.01  ------ Debug Options
% 27.42/4.01  
% 27.42/4.01  --dbg_backtrace                         false
% 27.42/4.01  --dbg_dump_prop_clauses                 false
% 27.42/4.01  --dbg_dump_prop_clauses_file            -
% 27.42/4.01  --dbg_out_stat                          false
% 27.42/4.01  ------ Parsing...
% 27.42/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.42/4.01  
% 27.42/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.42/4.01  
% 27.42/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.42/4.01  
% 27.42/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.42/4.01  ------ Proving...
% 27.42/4.01  ------ Problem Properties 
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  clauses                                 33
% 27.42/4.01  conjectures                             17
% 27.42/4.01  EPR                                     16
% 27.42/4.01  Horn                                    30
% 27.42/4.01  unary                                   17
% 27.42/4.01  binary                                  2
% 27.42/4.01  lits                                    128
% 27.42/4.01  lits eq                                 11
% 27.42/4.01  fd_pure                                 0
% 27.42/4.01  fd_pseudo                               0
% 27.42/4.01  fd_cond                                 0
% 27.42/4.01  fd_pseudo_cond                          0
% 27.42/4.01  AC symbols                              0
% 27.42/4.01  
% 27.42/4.01  ------ Schedule dynamic 5 is on 
% 27.42/4.01  
% 27.42/4.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  ------ 
% 27.42/4.01  Current options:
% 27.42/4.01  ------ 
% 27.42/4.01  
% 27.42/4.01  ------ Input Options
% 27.42/4.01  
% 27.42/4.01  --out_options                           all
% 27.42/4.01  --tptp_safe_out                         true
% 27.42/4.01  --problem_path                          ""
% 27.42/4.01  --include_path                          ""
% 27.42/4.01  --clausifier                            res/vclausify_rel
% 27.42/4.01  --clausifier_options                    --mode clausify
% 27.42/4.01  --stdin                                 false
% 27.42/4.01  --stats_out                             all
% 27.42/4.01  
% 27.42/4.01  ------ General Options
% 27.42/4.01  
% 27.42/4.01  --fof                                   false
% 27.42/4.01  --time_out_real                         305.
% 27.42/4.01  --time_out_virtual                      -1.
% 27.42/4.01  --symbol_type_check                     false
% 27.42/4.01  --clausify_out                          false
% 27.42/4.01  --sig_cnt_out                           false
% 27.42/4.01  --trig_cnt_out                          false
% 27.42/4.01  --trig_cnt_out_tolerance                1.
% 27.42/4.01  --trig_cnt_out_sk_spl                   false
% 27.42/4.01  --abstr_cl_out                          false
% 27.42/4.01  
% 27.42/4.01  ------ Global Options
% 27.42/4.01  
% 27.42/4.01  --schedule                              default
% 27.42/4.01  --add_important_lit                     false
% 27.42/4.01  --prop_solver_per_cl                    1000
% 27.42/4.01  --min_unsat_core                        false
% 27.42/4.01  --soft_assumptions                      false
% 27.42/4.01  --soft_lemma_size                       3
% 27.42/4.01  --prop_impl_unit_size                   0
% 27.42/4.01  --prop_impl_unit                        []
% 27.42/4.01  --share_sel_clauses                     true
% 27.42/4.01  --reset_solvers                         false
% 27.42/4.01  --bc_imp_inh                            [conj_cone]
% 27.42/4.01  --conj_cone_tolerance                   3.
% 27.42/4.01  --extra_neg_conj                        none
% 27.42/4.01  --large_theory_mode                     true
% 27.42/4.01  --prolific_symb_bound                   200
% 27.42/4.01  --lt_threshold                          2000
% 27.42/4.01  --clause_weak_htbl                      true
% 27.42/4.01  --gc_record_bc_elim                     false
% 27.42/4.01  
% 27.42/4.01  ------ Preprocessing Options
% 27.42/4.01  
% 27.42/4.01  --preprocessing_flag                    true
% 27.42/4.01  --time_out_prep_mult                    0.1
% 27.42/4.01  --splitting_mode                        input
% 27.42/4.01  --splitting_grd                         true
% 27.42/4.01  --splitting_cvd                         false
% 27.42/4.01  --splitting_cvd_svl                     false
% 27.42/4.01  --splitting_nvd                         32
% 27.42/4.01  --sub_typing                            true
% 27.42/4.01  --prep_gs_sim                           true
% 27.42/4.01  --prep_unflatten                        true
% 27.42/4.01  --prep_res_sim                          true
% 27.42/4.01  --prep_upred                            true
% 27.42/4.01  --prep_sem_filter                       exhaustive
% 27.42/4.01  --prep_sem_filter_out                   false
% 27.42/4.01  --pred_elim                             true
% 27.42/4.01  --res_sim_input                         true
% 27.42/4.01  --eq_ax_congr_red                       true
% 27.42/4.01  --pure_diseq_elim                       true
% 27.42/4.01  --brand_transform                       false
% 27.42/4.01  --non_eq_to_eq                          false
% 27.42/4.01  --prep_def_merge                        true
% 27.42/4.01  --prep_def_merge_prop_impl              false
% 27.42/4.01  --prep_def_merge_mbd                    true
% 27.42/4.01  --prep_def_merge_tr_red                 false
% 27.42/4.01  --prep_def_merge_tr_cl                  false
% 27.42/4.01  --smt_preprocessing                     true
% 27.42/4.01  --smt_ac_axioms                         fast
% 27.42/4.01  --preprocessed_out                      false
% 27.42/4.01  --preprocessed_stats                    false
% 27.42/4.01  
% 27.42/4.01  ------ Abstraction refinement Options
% 27.42/4.01  
% 27.42/4.01  --abstr_ref                             []
% 27.42/4.01  --abstr_ref_prep                        false
% 27.42/4.01  --abstr_ref_until_sat                   false
% 27.42/4.01  --abstr_ref_sig_restrict                funpre
% 27.42/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.42/4.01  --abstr_ref_under                       []
% 27.42/4.01  
% 27.42/4.01  ------ SAT Options
% 27.42/4.01  
% 27.42/4.01  --sat_mode                              false
% 27.42/4.01  --sat_fm_restart_options                ""
% 27.42/4.01  --sat_gr_def                            false
% 27.42/4.01  --sat_epr_types                         true
% 27.42/4.01  --sat_non_cyclic_types                  false
% 27.42/4.01  --sat_finite_models                     false
% 27.42/4.01  --sat_fm_lemmas                         false
% 27.42/4.01  --sat_fm_prep                           false
% 27.42/4.01  --sat_fm_uc_incr                        true
% 27.42/4.01  --sat_out_model                         small
% 27.42/4.01  --sat_out_clauses                       false
% 27.42/4.01  
% 27.42/4.01  ------ QBF Options
% 27.42/4.01  
% 27.42/4.01  --qbf_mode                              false
% 27.42/4.01  --qbf_elim_univ                         false
% 27.42/4.01  --qbf_dom_inst                          none
% 27.42/4.01  --qbf_dom_pre_inst                      false
% 27.42/4.01  --qbf_sk_in                             false
% 27.42/4.01  --qbf_pred_elim                         true
% 27.42/4.01  --qbf_split                             512
% 27.42/4.01  
% 27.42/4.01  ------ BMC1 Options
% 27.42/4.01  
% 27.42/4.01  --bmc1_incremental                      false
% 27.42/4.01  --bmc1_axioms                           reachable_all
% 27.42/4.01  --bmc1_min_bound                        0
% 27.42/4.01  --bmc1_max_bound                        -1
% 27.42/4.01  --bmc1_max_bound_default                -1
% 27.42/4.01  --bmc1_symbol_reachability              true
% 27.42/4.01  --bmc1_property_lemmas                  false
% 27.42/4.01  --bmc1_k_induction                      false
% 27.42/4.01  --bmc1_non_equiv_states                 false
% 27.42/4.01  --bmc1_deadlock                         false
% 27.42/4.01  --bmc1_ucm                              false
% 27.42/4.01  --bmc1_add_unsat_core                   none
% 27.42/4.01  --bmc1_unsat_core_children              false
% 27.42/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.42/4.01  --bmc1_out_stat                         full
% 27.42/4.01  --bmc1_ground_init                      false
% 27.42/4.01  --bmc1_pre_inst_next_state              false
% 27.42/4.01  --bmc1_pre_inst_state                   false
% 27.42/4.01  --bmc1_pre_inst_reach_state             false
% 27.42/4.01  --bmc1_out_unsat_core                   false
% 27.42/4.01  --bmc1_aig_witness_out                  false
% 27.42/4.01  --bmc1_verbose                          false
% 27.42/4.01  --bmc1_dump_clauses_tptp                false
% 27.42/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.42/4.01  --bmc1_dump_file                        -
% 27.42/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.42/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.42/4.01  --bmc1_ucm_extend_mode                  1
% 27.42/4.01  --bmc1_ucm_init_mode                    2
% 27.42/4.01  --bmc1_ucm_cone_mode                    none
% 27.42/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.42/4.01  --bmc1_ucm_relax_model                  4
% 27.42/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.42/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.42/4.01  --bmc1_ucm_layered_model                none
% 27.42/4.01  --bmc1_ucm_max_lemma_size               10
% 27.42/4.01  
% 27.42/4.01  ------ AIG Options
% 27.42/4.01  
% 27.42/4.01  --aig_mode                              false
% 27.42/4.01  
% 27.42/4.01  ------ Instantiation Options
% 27.42/4.01  
% 27.42/4.01  --instantiation_flag                    true
% 27.42/4.01  --inst_sos_flag                         false
% 27.42/4.01  --inst_sos_phase                        true
% 27.42/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.42/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.42/4.01  --inst_lit_sel_side                     none
% 27.42/4.01  --inst_solver_per_active                1400
% 27.42/4.01  --inst_solver_calls_frac                1.
% 27.42/4.01  --inst_passive_queue_type               priority_queues
% 27.42/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.42/4.01  --inst_passive_queues_freq              [25;2]
% 27.42/4.01  --inst_dismatching                      true
% 27.42/4.01  --inst_eager_unprocessed_to_passive     true
% 27.42/4.01  --inst_prop_sim_given                   true
% 27.42/4.01  --inst_prop_sim_new                     false
% 27.42/4.01  --inst_subs_new                         false
% 27.42/4.01  --inst_eq_res_simp                      false
% 27.42/4.01  --inst_subs_given                       false
% 27.42/4.01  --inst_orphan_elimination               true
% 27.42/4.01  --inst_learning_loop_flag               true
% 27.42/4.01  --inst_learning_start                   3000
% 27.42/4.01  --inst_learning_factor                  2
% 27.42/4.01  --inst_start_prop_sim_after_learn       3
% 27.42/4.01  --inst_sel_renew                        solver
% 27.42/4.01  --inst_lit_activity_flag                true
% 27.42/4.01  --inst_restr_to_given                   false
% 27.42/4.01  --inst_activity_threshold               500
% 27.42/4.01  --inst_out_proof                        true
% 27.42/4.01  
% 27.42/4.01  ------ Resolution Options
% 27.42/4.01  
% 27.42/4.01  --resolution_flag                       false
% 27.42/4.01  --res_lit_sel                           adaptive
% 27.42/4.01  --res_lit_sel_side                      none
% 27.42/4.01  --res_ordering                          kbo
% 27.42/4.01  --res_to_prop_solver                    active
% 27.42/4.01  --res_prop_simpl_new                    false
% 27.42/4.01  --res_prop_simpl_given                  true
% 27.42/4.01  --res_passive_queue_type                priority_queues
% 27.42/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.42/4.01  --res_passive_queues_freq               [15;5]
% 27.42/4.01  --res_forward_subs                      full
% 27.42/4.01  --res_backward_subs                     full
% 27.42/4.01  --res_forward_subs_resolution           true
% 27.42/4.01  --res_backward_subs_resolution          true
% 27.42/4.01  --res_orphan_elimination                true
% 27.42/4.01  --res_time_limit                        2.
% 27.42/4.01  --res_out_proof                         true
% 27.42/4.01  
% 27.42/4.01  ------ Superposition Options
% 27.42/4.01  
% 27.42/4.01  --superposition_flag                    true
% 27.42/4.01  --sup_passive_queue_type                priority_queues
% 27.42/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.42/4.01  --sup_passive_queues_freq               [8;1;4]
% 27.42/4.01  --demod_completeness_check              fast
% 27.42/4.01  --demod_use_ground                      true
% 27.42/4.01  --sup_to_prop_solver                    passive
% 27.42/4.01  --sup_prop_simpl_new                    true
% 27.42/4.01  --sup_prop_simpl_given                  true
% 27.42/4.01  --sup_fun_splitting                     false
% 27.42/4.01  --sup_smt_interval                      50000
% 27.42/4.01  
% 27.42/4.01  ------ Superposition Simplification Setup
% 27.42/4.01  
% 27.42/4.01  --sup_indices_passive                   []
% 27.42/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.42/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.01  --sup_full_bw                           [BwDemod]
% 27.42/4.01  --sup_immed_triv                        [TrivRules]
% 27.42/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.01  --sup_immed_bw_main                     []
% 27.42/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.42/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.01  
% 27.42/4.01  ------ Combination Options
% 27.42/4.01  
% 27.42/4.01  --comb_res_mult                         3
% 27.42/4.01  --comb_sup_mult                         2
% 27.42/4.01  --comb_inst_mult                        10
% 27.42/4.01  
% 27.42/4.01  ------ Debug Options
% 27.42/4.01  
% 27.42/4.01  --dbg_backtrace                         false
% 27.42/4.01  --dbg_dump_prop_clauses                 false
% 27.42/4.01  --dbg_dump_prop_clauses_file            -
% 27.42/4.01  --dbg_out_stat                          false
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  ------ Proving...
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  % SZS status Theorem for theBenchmark.p
% 27.42/4.01  
% 27.42/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.42/4.01  
% 27.42/4.01  fof(f11,axiom,(
% 27.42/4.01    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f31,plain,(
% 27.42/4.01    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 27.42/4.01    inference(ennf_transformation,[],[f11])).
% 27.42/4.01  
% 27.42/4.01  fof(f68,plain,(
% 27.42/4.01    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f31])).
% 27.42/4.01  
% 27.42/4.01  fof(f14,conjecture,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f15,negated_conjecture,(
% 27.42/4.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 27.42/4.01    inference(negated_conjecture,[],[f14])).
% 27.42/4.01  
% 27.42/4.01  fof(f36,plain,(
% 27.42/4.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f15])).
% 27.42/4.01  
% 27.42/4.01  fof(f37,plain,(
% 27.42/4.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.42/4.01    inference(flattening,[],[f36])).
% 27.42/4.01  
% 27.42/4.01  fof(f50,plain,(
% 27.42/4.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 27.42/4.01    introduced(choice_axiom,[])).
% 27.42/4.01  
% 27.42/4.01  fof(f49,plain,(
% 27.42/4.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 27.42/4.01    introduced(choice_axiom,[])).
% 27.42/4.01  
% 27.42/4.01  fof(f48,plain,(
% 27.42/4.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 27.42/4.01    introduced(choice_axiom,[])).
% 27.42/4.01  
% 27.42/4.01  fof(f47,plain,(
% 27.42/4.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 27.42/4.01    introduced(choice_axiom,[])).
% 27.42/4.01  
% 27.42/4.01  fof(f46,plain,(
% 27.42/4.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 27.42/4.01    introduced(choice_axiom,[])).
% 27.42/4.01  
% 27.42/4.01  fof(f45,plain,(
% 27.42/4.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 27.42/4.01    introduced(choice_axiom,[])).
% 27.42/4.01  
% 27.42/4.01  fof(f44,plain,(
% 27.42/4.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 27.42/4.01    introduced(choice_axiom,[])).
% 27.42/4.01  
% 27.42/4.01  fof(f51,plain,(
% 27.42/4.01    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 27.42/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f37,f50,f49,f48,f47,f46,f45,f44])).
% 27.42/4.01  
% 27.42/4.01  fof(f79,plain,(
% 27.42/4.01    m1_pre_topc(sK2,sK0)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f4,axiom,(
% 27.42/4.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f20,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 27.42/4.01    inference(ennf_transformation,[],[f4])).
% 27.42/4.01  
% 27.42/4.01  fof(f55,plain,(
% 27.42/4.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f20])).
% 27.42/4.01  
% 27.42/4.01  fof(f74,plain,(
% 27.42/4.01    l1_pre_topc(sK0)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f3,axiom,(
% 27.42/4.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f19,plain,(
% 27.42/4.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 27.42/4.01    inference(ennf_transformation,[],[f3])).
% 27.42/4.01  
% 27.42/4.01  fof(f54,plain,(
% 27.42/4.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f19])).
% 27.42/4.01  
% 27.42/4.01  fof(f2,axiom,(
% 27.42/4.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f18,plain,(
% 27.42/4.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 27.42/4.01    inference(ennf_transformation,[],[f2])).
% 27.42/4.01  
% 27.42/4.01  fof(f53,plain,(
% 27.42/4.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f18])).
% 27.42/4.01  
% 27.42/4.01  fof(f5,axiom,(
% 27.42/4.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f21,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.42/4.01    inference(ennf_transformation,[],[f5])).
% 27.42/4.01  
% 27.42/4.01  fof(f38,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.42/4.01    inference(nnf_transformation,[],[f21])).
% 27.42/4.01  
% 27.42/4.01  fof(f56,plain,(
% 27.42/4.01    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f38])).
% 27.42/4.01  
% 27.42/4.01  fof(f85,plain,(
% 27.42/4.01    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f7,axiom,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f24,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f7])).
% 27.42/4.01  
% 27.42/4.01  fof(f25,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.42/4.01    inference(flattening,[],[f24])).
% 27.42/4.01  
% 27.42/4.01  fof(f59,plain,(
% 27.42/4.01    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f25])).
% 27.42/4.01  
% 27.42/4.01  fof(f83,plain,(
% 27.42/4.01    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f82,plain,(
% 27.42/4.01    v1_funct_1(sK4)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f12,axiom,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f32,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f12])).
% 27.42/4.01  
% 27.42/4.01  fof(f33,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(flattening,[],[f32])).
% 27.42/4.01  
% 27.42/4.01  fof(f69,plain,(
% 27.42/4.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f33])).
% 27.42/4.01  
% 27.42/4.01  fof(f75,plain,(
% 27.42/4.01    ~v2_struct_0(sK1)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f76,plain,(
% 27.42/4.01    v2_pre_topc(sK1)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f77,plain,(
% 27.42/4.01    l1_pre_topc(sK1)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f84,plain,(
% 27.42/4.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f81,plain,(
% 27.42/4.01    m1_pre_topc(sK3,sK0)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f73,plain,(
% 27.42/4.01    v2_pre_topc(sK0)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f80,plain,(
% 27.42/4.01    ~v2_struct_0(sK3)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f1,axiom,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f16,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f1])).
% 27.42/4.01  
% 27.42/4.01  fof(f17,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(flattening,[],[f16])).
% 27.42/4.01  
% 27.42/4.01  fof(f52,plain,(
% 27.42/4.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f17])).
% 27.42/4.01  
% 27.42/4.01  fof(f72,plain,(
% 27.42/4.01    ~v2_struct_0(sK0)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f89,plain,(
% 27.42/4.01    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f88,plain,(
% 27.42/4.01    sK5 = sK6),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f13,axiom,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f34,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f13])).
% 27.42/4.01  
% 27.42/4.01  fof(f35,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.42/4.01    inference(flattening,[],[f34])).
% 27.42/4.01  
% 27.42/4.01  fof(f43,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.42/4.01    inference(nnf_transformation,[],[f35])).
% 27.42/4.01  
% 27.42/4.01  fof(f71,plain,(
% 27.42/4.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f43])).
% 27.42/4.01  
% 27.42/4.01  fof(f98,plain,(
% 27.42/4.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.42/4.01    inference(equality_resolution,[],[f71])).
% 27.42/4.01  
% 27.42/4.01  fof(f8,axiom,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f26,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f8])).
% 27.42/4.01  
% 27.42/4.01  fof(f27,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(flattening,[],[f26])).
% 27.42/4.01  
% 27.42/4.01  fof(f39,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(nnf_transformation,[],[f27])).
% 27.42/4.01  
% 27.42/4.01  fof(f40,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(flattening,[],[f39])).
% 27.42/4.01  
% 27.42/4.01  fof(f62,plain,(
% 27.42/4.01    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f40])).
% 27.42/4.01  
% 27.42/4.01  fof(f92,plain,(
% 27.42/4.01    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.42/4.01    inference(equality_resolution,[],[f62])).
% 27.42/4.01  
% 27.42/4.01  fof(f6,axiom,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f22,plain,(
% 27.42/4.01    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f6])).
% 27.42/4.01  
% 27.42/4.01  fof(f23,plain,(
% 27.42/4.01    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(flattening,[],[f22])).
% 27.42/4.01  
% 27.42/4.01  fof(f58,plain,(
% 27.42/4.01    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f23])).
% 27.42/4.01  
% 27.42/4.01  fof(f9,axiom,(
% 27.42/4.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f28,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.42/4.01    inference(ennf_transformation,[],[f9])).
% 27.42/4.01  
% 27.42/4.01  fof(f29,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(flattening,[],[f28])).
% 27.42/4.01  
% 27.42/4.01  fof(f41,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(nnf_transformation,[],[f29])).
% 27.42/4.01  
% 27.42/4.01  fof(f42,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.42/4.01    inference(flattening,[],[f41])).
% 27.42/4.01  
% 27.42/4.01  fof(f65,plain,(
% 27.42/4.01    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f42])).
% 27.42/4.01  
% 27.42/4.01  fof(f96,plain,(
% 27.42/4.01    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.42/4.01    inference(equality_resolution,[],[f65])).
% 27.42/4.01  
% 27.42/4.01  fof(f10,axiom,(
% 27.42/4.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.42/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.01  
% 27.42/4.01  fof(f30,plain,(
% 27.42/4.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 27.42/4.01    inference(ennf_transformation,[],[f10])).
% 27.42/4.01  
% 27.42/4.01  fof(f67,plain,(
% 27.42/4.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 27.42/4.01    inference(cnf_transformation,[],[f30])).
% 27.42/4.01  
% 27.42/4.01  fof(f87,plain,(
% 27.42/4.01    m1_subset_1(sK6,u1_struct_0(sK2))),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f90,plain,(
% 27.42/4.01    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f86,plain,(
% 27.42/4.01    m1_subset_1(sK5,u1_struct_0(sK3))),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  fof(f78,plain,(
% 27.42/4.01    ~v2_struct_0(sK2)),
% 27.42/4.01    inference(cnf_transformation,[],[f51])).
% 27.42/4.01  
% 27.42/4.01  cnf(c_16,plain,
% 27.42/4.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f68]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_871,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_16]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1461,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_871]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_31,negated_conjecture,
% 27.42/4.01      ( m1_pre_topc(sK2,sK0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f79]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_860,negated_conjecture,
% 27.42/4.01      ( m1_pre_topc(sK2,sK0) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_31]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1470,plain,
% 27.42/4.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_3,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f55]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_876,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | l1_pre_topc(X0_54) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_3]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1456,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2378,plain,
% 27.42/4.01      ( l1_pre_topc(sK0) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK2) = iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1470,c_1456]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_36,negated_conjecture,
% 27.42/4.01      ( l1_pre_topc(sK0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f74]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_41,plain,
% 27.42/4.01      ( l1_pre_topc(sK0) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2694,plain,
% 27.42/4.01      ( l1_pre_topc(sK2) = iProver_top ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_2378,c_41]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2,plain,
% 27.42/4.01      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f54]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1,plain,
% 27.42/4.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f53]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_406,plain,
% 27.42/4.01      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.42/4.01      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_849,plain,
% 27.42/4.01      ( ~ l1_pre_topc(X0_54) | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_406]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1481,plain,
% 27.42/4.01      ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_3188,plain,
% 27.42/4.01      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_2694,c_1481]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_5,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.42/4.01      | ~ l1_pre_topc(X0)
% 27.42/4.01      | ~ l1_pre_topc(X1) ),
% 27.42/4.01      inference(cnf_transformation,[],[f56]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_230,plain,
% 27.42/4.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.42/4.01      | ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ l1_pre_topc(X1) ),
% 27.42/4.01      inference(global_propositional_subsumption,[status(thm)],[c_5,c_3]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_231,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.42/4.01      | ~ l1_pre_topc(X1) ),
% 27.42/4.01      inference(renaming,[status(thm)],[c_230]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_850,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.42/4.01      | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)))
% 27.42/4.01      | ~ l1_pre_topc(X1_54) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_231]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1480,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))) = iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_5894,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,sK2) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK2) != iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_3188,c_1480]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_25,negated_conjecture,
% 27.42/4.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 27.42/4.01      inference(cnf_transformation,[],[f85]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_864,negated_conjecture,
% 27.42/4.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_25]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_3849,plain,
% 27.42/4.01      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 27.42/4.01      inference(demodulation,[status(thm)],[c_3188,c_864]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_5978,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,sK3) = iProver_top
% 27.42/4.01      | l1_pre_topc(sK2) != iProver_top ),
% 27.42/4.01      inference(light_normalisation,[status(thm)],[c_5894,c_3849]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_6054,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,sK3) = iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_5978,c_41,c_2378]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_6055,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,sK3) = iProver_top ),
% 27.42/4.01      inference(renaming,[status(thm)],[c_6054]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_6063,plain,
% 27.42/4.01      ( m1_pre_topc(sK2,sK3) = iProver_top
% 27.42/4.01      | l1_pre_topc(sK2) != iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1461,c_6055]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_6105,plain,
% 27.42/4.01      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_6063,c_41,c_2378]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_7,plain,
% 27.42/4.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.42/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.42/4.01      | ~ m1_pre_topc(X3,X1)
% 27.42/4.01      | ~ m1_pre_topc(X3,X4)
% 27.42/4.01      | ~ m1_pre_topc(X1,X4)
% 27.42/4.01      | v2_struct_0(X4)
% 27.42/4.01      | v2_struct_0(X2)
% 27.42/4.01      | ~ v1_funct_1(X0)
% 27.42/4.01      | ~ l1_pre_topc(X4)
% 27.42/4.01      | ~ l1_pre_topc(X2)
% 27.42/4.01      | ~ v2_pre_topc(X4)
% 27.42/4.01      | ~ v2_pre_topc(X2)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f59]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_27,negated_conjecture,
% 27.42/4.01      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 27.42/4.01      inference(cnf_transformation,[],[f83]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_448,plain,
% 27.42/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.42/4.01      | ~ m1_pre_topc(X3,X1)
% 27.42/4.01      | ~ m1_pre_topc(X3,X4)
% 27.42/4.01      | ~ m1_pre_topc(X1,X4)
% 27.42/4.01      | v2_struct_0(X4)
% 27.42/4.01      | v2_struct_0(X2)
% 27.42/4.01      | ~ v1_funct_1(X0)
% 27.42/4.01      | ~ l1_pre_topc(X4)
% 27.42/4.01      | ~ l1_pre_topc(X2)
% 27.42/4.01      | ~ v2_pre_topc(X4)
% 27.42/4.01      | ~ v2_pre_topc(X2)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 27.42/4.01      | u1_struct_0(X2) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK3)
% 27.42/4.01      | sK4 != X0 ),
% 27.42/4.01      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_449,plain,
% 27.42/4.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_pre_topc(X2,X0)
% 27.42/4.01      | ~ m1_pre_topc(X2,X3)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | ~ v1_funct_1(sK4)
% 27.42/4.01      | ~ l1_pre_topc(X3)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X3)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(unflattening,[status(thm)],[c_448]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_28,negated_conjecture,
% 27.42/4.01      ( v1_funct_1(sK4) ),
% 27.42/4.01      inference(cnf_transformation,[],[f82]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_453,plain,
% 27.42/4.01      ( v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | ~ m1_pre_topc(X2,X3)
% 27.42/4.01      | ~ m1_pre_topc(X2,X0)
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.42/4.01      | ~ l1_pre_topc(X3)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X3)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_449,c_28]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_454,plain,
% 27.42/4.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_pre_topc(X2,X0)
% 27.42/4.01      | ~ m1_pre_topc(X2,X3)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X3)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X3)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(renaming,[status(thm)],[c_453]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_17,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ m1_pre_topc(X2,X0)
% 27.42/4.01      | m1_pre_topc(X2,X1)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X1) ),
% 27.42/4.01      inference(cnf_transformation,[],[f69]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_485,plain,
% 27.42/4.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_pre_topc(X2,X0)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X3)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X3)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(forward_subsumption_resolution,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_454,c_17]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_847,plain,
% 27.42/4.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 27.42/4.01      | ~ m1_pre_topc(X0_54,X2_54)
% 27.42/4.01      | ~ m1_pre_topc(X3_54,X0_54)
% 27.42/4.01      | v2_struct_0(X1_54)
% 27.42/4.01      | v2_struct_0(X2_54)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X2_54)
% 27.42/4.01      | ~ v2_pre_topc(X1_54)
% 27.42/4.01      | ~ v2_pre_topc(X2_54)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4,u1_struct_0(X3_54)) = k3_tmap_1(X2_54,X1_54,X0_54,X3_54,sK4)
% 27.42/4.01      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_485]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1483,plain,
% 27.42/4.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,sK4)
% 27.42/4.01      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 27.42/4.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 27.42/4.01      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X1_54) = iProver_top
% 27.42/4.01      | v2_struct_0(X3_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X3_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X3_54) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2369,plain,
% 27.42/4.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4)
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 27.42/4.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X2_54) = iProver_top
% 27.42/4.01      | v2_struct_0(sK1) = iProver_top
% 27.42/4.01      | l1_pre_topc(X2_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK1) != iProver_top
% 27.42/4.01      | v2_pre_topc(X2_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK1) != iProver_top ),
% 27.42/4.01      inference(equality_resolution,[status(thm)],[c_1483]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_35,negated_conjecture,
% 27.42/4.01      ( ~ v2_struct_0(sK1) ),
% 27.42/4.01      inference(cnf_transformation,[],[f75]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_42,plain,
% 27.42/4.01      ( v2_struct_0(sK1) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_34,negated_conjecture,
% 27.42/4.01      ( v2_pre_topc(sK1) ),
% 27.42/4.01      inference(cnf_transformation,[],[f76]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_43,plain,
% 27.42/4.01      ( v2_pre_topc(sK1) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_33,negated_conjecture,
% 27.42/4.01      ( l1_pre_topc(sK1) ),
% 27.42/4.01      inference(cnf_transformation,[],[f77]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_44,plain,
% 27.42/4.01      ( l1_pre_topc(sK1) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2937,plain,
% 27.42/4.01      ( v2_pre_topc(X2_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X2_54) = iProver_top
% 27.42/4.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 27.42/4.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 27.42/4.01      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4)
% 27.42/4.01      | l1_pre_topc(X2_54) != iProver_top ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_2369,c_42,c_43,c_44]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2938,plain,
% 27.42/4.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4)
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 27.42/4.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X2_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X2_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X2_54) != iProver_top ),
% 27.42/4.01      inference(renaming,[status(thm)],[c_2937]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2949,plain,
% 27.42/4.01      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
% 27.42/4.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 27.42/4.01      | m1_pre_topc(X0_54,sK3) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,X1_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X1_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X1_54) != iProver_top ),
% 27.42/4.01      inference(equality_resolution,[status(thm)],[c_2938]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_26,negated_conjecture,
% 27.42/4.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 27.42/4.01      inference(cnf_transformation,[],[f84]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_51,plain,
% 27.42/4.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9847,plain,
% 27.42/4.01      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
% 27.42/4.01      | m1_pre_topc(X0_54,sK3) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,X1_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X1_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X1_54) != iProver_top ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_2949,c_51]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_858,negated_conjecture,
% 27.42/4.01      ( l1_pre_topc(sK1) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_33]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1472,plain,
% 27.42/4.01      ( l1_pre_topc(sK1) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_3185,plain,
% 27.42/4.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1472,c_1481]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_29,negated_conjecture,
% 27.42/4.01      ( m1_pre_topc(sK3,sK0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f81]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_862,negated_conjecture,
% 27.42/4.01      ( m1_pre_topc(sK3,sK0) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_29]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1468,plain,
% 27.42/4.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2377,plain,
% 27.42/4.01      ( l1_pre_topc(sK0) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK3) = iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1468,c_1456]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_2688,plain,
% 27.42/4.01      ( l1_pre_topc(sK3) = iProver_top ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_2377,c_41]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_3187,plain,
% 27.42/4.01      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_2688,c_1481]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9853,plain,
% 27.42/4.01      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
% 27.42/4.01      | m1_pre_topc(X0_54,sK3) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,X1_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X1_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X1_54) != iProver_top ),
% 27.42/4.01      inference(light_normalisation,[status(thm)],[c_9847,c_3185,c_3187]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9868,plain,
% 27.42/4.01      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_54,sK1,sK3,sK2,sK4)
% 27.42/4.01      | m1_pre_topc(sK3,X0_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X0_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_6105,c_9853]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9921,plain,
% 27.42/4.01      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(X0_54,sK1,sK3,sK2,sK4)
% 27.42/4.01      | m1_pre_topc(sK3,X0_54) != iProver_top
% 27.42/4.01      | v2_struct_0(X0_54) = iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top ),
% 27.42/4.01      inference(light_normalisation,[status(thm)],[c_9868,c_3188]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_123073,plain,
% 27.42/4.01      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)
% 27.42/4.01      | v2_struct_0(sK3) = iProver_top
% 27.42/4.01      | l1_pre_topc(sK3) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK3) != iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1461,c_9921]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_37,negated_conjecture,
% 27.42/4.01      ( v2_pre_topc(sK0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f73]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_40,plain,
% 27.42/4.01      ( v2_pre_topc(sK0) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_30,negated_conjecture,
% 27.42/4.01      ( ~ v2_struct_0(sK3) ),
% 27.42/4.01      inference(cnf_transformation,[],[f80]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_47,plain,
% 27.42/4.01      ( v2_struct_0(sK3) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_0,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | v2_pre_topc(X0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f52]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_877,plain,
% 27.42/4.01      ( ~ m1_pre_topc(X0_54,X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | ~ v2_pre_topc(X1_54)
% 27.42/4.01      | v2_pre_topc(X0_54) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_0]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1455,plain,
% 27.42/4.01      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1883,plain,
% 27.42/4.01      ( l1_pre_topc(sK0) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK0) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK3) = iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1468,c_1455]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_123477,plain,
% 27.42/4.01      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_123073,c_40,c_41,c_47,c_1883,c_2377]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_123068,plain,
% 27.42/4.01      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 27.42/4.01      | v2_struct_0(sK0) = iProver_top
% 27.42/4.01      | l1_pre_topc(sK0) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK0) != iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1468,c_9921]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_38,negated_conjecture,
% 27.42/4.01      ( ~ v2_struct_0(sK0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f72]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_39,plain,
% 27.42/4.01      ( v2_struct_0(sK0) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_123469,plain,
% 27.42/4.01      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_123068,c_39,c_40,c_41]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_123480,plain,
% 27.42/4.01      ( k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
% 27.42/4.01      inference(demodulation,[status(thm)],[c_123477,c_123469]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_21,negated_conjecture,
% 27.42/4.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 27.42/4.01      inference(cnf_transformation,[],[f89]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_868,negated_conjecture,
% 27.42/4.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_21]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1464,plain,
% 27.42/4.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_22,negated_conjecture,
% 27.42/4.01      ( sK5 = sK6 ),
% 27.42/4.01      inference(cnf_transformation,[],[f88]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_867,negated_conjecture,
% 27.42/4.01      ( sK5 = sK6 ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_22]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1527,plain,
% 27.42/4.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 27.42/4.01      inference(light_normalisation,[status(thm)],[c_1464,c_867]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_127332,plain,
% 27.42/4.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 27.42/4.01      inference(demodulation,[status(thm)],[c_123480,c_1527]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_18,plain,
% 27.42/4.01      ( r1_tmap_1(X0,X1,X2,X3)
% 27.42/4.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 27.42/4.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 27.42/4.01      | ~ v1_tsep_1(X4,X5)
% 27.42/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 27.42/4.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.42/4.01      | ~ m1_pre_topc(X4,X5)
% 27.42/4.01      | ~ m1_pre_topc(X4,X0)
% 27.42/4.01      | ~ m1_pre_topc(X0,X5)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X5)
% 27.42/4.01      | v2_struct_0(X4)
% 27.42/4.01      | v2_struct_0(X0)
% 27.42/4.01      | ~ v1_funct_1(X2)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X5)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X5) ),
% 27.42/4.01      inference(cnf_transformation,[],[f98]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_568,plain,
% 27.42/4.01      ( r1_tmap_1(X0,X1,X2,X3)
% 27.42/4.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 27.42/4.01      | ~ v1_tsep_1(X4,X5)
% 27.42/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 27.42/4.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.42/4.01      | ~ m1_pre_topc(X4,X5)
% 27.42/4.01      | ~ m1_pre_topc(X4,X0)
% 27.42/4.01      | ~ m1_pre_topc(X0,X5)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X0)
% 27.42/4.01      | v2_struct_0(X4)
% 27.42/4.01      | v2_struct_0(X5)
% 27.42/4.01      | ~ v1_funct_1(X2)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X5)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X5)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 27.42/4.01      | sK4 != X2 ),
% 27.42/4.01      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_569,plain,
% 27.42/4.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.42/4.01      | r1_tmap_1(X3,X1,sK4,X4)
% 27.42/4.01      | ~ v1_tsep_1(X0,X2)
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_pre_topc(X0,X2)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | ~ m1_pre_topc(X3,X2)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | v2_struct_0(X0)
% 27.42/4.01      | v2_struct_0(X2)
% 27.42/4.01      | ~ v1_funct_1(sK4)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X2)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X2)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(unflattening,[status(thm)],[c_568]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_573,plain,
% 27.42/4.01      ( v2_struct_0(X2)
% 27.42/4.01      | v2_struct_0(X0)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | ~ m1_pre_topc(X3,X2)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | ~ m1_pre_topc(X0,X2)
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.42/4.01      | ~ v1_tsep_1(X0,X2)
% 27.42/4.01      | r1_tmap_1(X3,X1,sK4,X4)
% 27.42/4.01      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X2)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X2)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_569,c_28]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_574,plain,
% 27.42/4.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.42/4.01      | r1_tmap_1(X3,X1,sK4,X4)
% 27.42/4.01      | ~ v1_tsep_1(X0,X2)
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_pre_topc(X3,X2)
% 27.42/4.01      | ~ m1_pre_topc(X0,X2)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X0)
% 27.42/4.01      | v2_struct_0(X2)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X2)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X2)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(renaming,[status(thm)],[c_573]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_617,plain,
% 27.42/4.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.42/4.01      | r1_tmap_1(X3,X1,sK4,X4)
% 27.42/4.01      | ~ v1_tsep_1(X0,X2)
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.42/4.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.42/4.01      | ~ m1_pre_topc(X3,X2)
% 27.42/4.01      | ~ m1_pre_topc(X0,X3)
% 27.42/4.01      | v2_struct_0(X1)
% 27.42/4.01      | v2_struct_0(X0)
% 27.42/4.01      | v2_struct_0(X2)
% 27.42/4.01      | v2_struct_0(X3)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X2)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X2)
% 27.42/4.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(forward_subsumption_resolution,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_574,c_17]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_845,plain,
% 27.42/4.01      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
% 27.42/4.01      | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
% 27.42/4.01      | ~ v1_tsep_1(X0_54,X2_54)
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 27.42/4.01      | ~ m1_pre_topc(X3_54,X2_54)
% 27.42/4.01      | ~ m1_pre_topc(X0_54,X3_54)
% 27.42/4.01      | v2_struct_0(X1_54)
% 27.42/4.01      | v2_struct_0(X0_54)
% 27.42/4.01      | v2_struct_0(X2_54)
% 27.42/4.01      | v2_struct_0(X3_54)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X2_54)
% 27.42/4.01      | ~ v2_pre_topc(X1_54)
% 27.42/4.01      | ~ v2_pre_topc(X2_54)
% 27.42/4.01      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_617]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1822,plain,
% 27.42/4.01      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,sK3,X0_54,sK4),X0_55)
% 27.42/4.01      | r1_tmap_1(sK3,X1_54,sK4,X0_55)
% 27.42/4.01      | ~ v1_tsep_1(X0_54,X2_54)
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_54))))
% 27.42/4.01      | ~ m1_pre_topc(X0_54,sK3)
% 27.42/4.01      | ~ m1_pre_topc(sK3,X2_54)
% 27.42/4.01      | v2_struct_0(X1_54)
% 27.42/4.01      | v2_struct_0(X0_54)
% 27.42/4.01      | v2_struct_0(X2_54)
% 27.42/4.01      | v2_struct_0(sK3)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X2_54)
% 27.42/4.01      | ~ v2_pre_topc(X1_54)
% 27.42/4.01      | ~ v2_pre_topc(X2_54)
% 27.42/4.01      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_845]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_11020,plain,
% 27.42/4.01      ( ~ r1_tmap_1(sK2,X0_54,k3_tmap_1(X1_54,X0_54,sK3,sK2,sK4),X0_55)
% 27.42/4.01      | r1_tmap_1(sK3,X0_54,sK4,X0_55)
% 27.42/4.01      | ~ v1_tsep_1(sK2,X1_54)
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK2))
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
% 27.42/4.01      | ~ m1_pre_topc(sK2,sK3)
% 27.42/4.01      | ~ m1_pre_topc(sK3,X1_54)
% 27.42/4.01      | v2_struct_0(X1_54)
% 27.42/4.01      | v2_struct_0(X0_54)
% 27.42/4.01      | v2_struct_0(sK2)
% 27.42/4.01      | v2_struct_0(sK3)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X0_54)
% 27.42/4.01      | ~ v2_pre_topc(X1_54)
% 27.42/4.01      | ~ v2_pre_topc(X0_54)
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_1822]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_20803,plain,
% 27.42/4.01      ( ~ r1_tmap_1(sK2,X0_54,k3_tmap_1(sK3,X0_54,sK3,sK2,sK4),X0_55)
% 27.42/4.01      | r1_tmap_1(sK3,X0_54,sK4,X0_55)
% 27.42/4.01      | ~ v1_tsep_1(sK2,sK3)
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK2))
% 27.42/4.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
% 27.42/4.01      | ~ m1_pre_topc(sK2,sK3)
% 27.42/4.01      | ~ m1_pre_topc(sK3,sK3)
% 27.42/4.01      | v2_struct_0(X0_54)
% 27.42/4.01      | v2_struct_0(sK2)
% 27.42/4.01      | v2_struct_0(sK3)
% 27.42/4.01      | ~ l1_pre_topc(X0_54)
% 27.42/4.01      | ~ l1_pre_topc(sK3)
% 27.42/4.01      | ~ v2_pre_topc(X0_54)
% 27.42/4.01      | ~ v2_pre_topc(sK3)
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_11020]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_47272,plain,
% 27.42/4.01      ( ~ r1_tmap_1(sK2,X0_54,k3_tmap_1(sK3,X0_54,sK3,sK2,sK4),sK5)
% 27.42/4.01      | r1_tmap_1(sK3,X0_54,sK4,sK5)
% 27.42/4.01      | ~ v1_tsep_1(sK2,sK3)
% 27.42/4.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 27.42/4.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 27.42/4.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54))))
% 27.42/4.01      | ~ m1_pre_topc(sK2,sK3)
% 27.42/4.01      | ~ m1_pre_topc(sK3,sK3)
% 27.42/4.01      | v2_struct_0(X0_54)
% 27.42/4.01      | v2_struct_0(sK2)
% 27.42/4.01      | v2_struct_0(sK3)
% 27.42/4.01      | ~ l1_pre_topc(X0_54)
% 27.42/4.01      | ~ l1_pre_topc(sK3)
% 27.42/4.01      | ~ v2_pre_topc(X0_54)
% 27.42/4.01      | ~ v2_pre_topc(sK3)
% 27.42/4.01      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_20803]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_47273,plain,
% 27.42/4.01      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 27.42/4.01      | r1_tmap_1(sK2,X0_54,k3_tmap_1(sK3,X0_54,sK3,sK2,sK4),sK5) != iProver_top
% 27.42/4.01      | r1_tmap_1(sK3,X0_54,sK4,sK5) = iProver_top
% 27.42/4.01      | v1_tsep_1(sK2,sK3) != iProver_top
% 27.42/4.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.42/4.01      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 27.42/4.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,sK3) != iProver_top
% 27.42/4.01      | v2_struct_0(X0_54) = iProver_top
% 27.42/4.01      | v2_struct_0(sK2) = iProver_top
% 27.42/4.01      | v2_struct_0(sK3) = iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK3) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK3) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_47272]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_47275,plain,
% 27.42/4.01      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.42/4.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 27.42/4.01      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK2,sK4),sK5) != iProver_top
% 27.42/4.01      | r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 27.42/4.01      | v1_tsep_1(sK2,sK3) != iProver_top
% 27.42/4.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 27.42/4.01      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 27.42/4.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,sK3) != iProver_top
% 27.42/4.01      | v2_struct_0(sK2) = iProver_top
% 27.42/4.01      | v2_struct_0(sK1) = iProver_top
% 27.42/4.01      | v2_struct_0(sK3) = iProver_top
% 27.42/4.01      | l1_pre_topc(sK1) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK3) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK1) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK3) != iProver_top ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_47273]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9,plain,
% 27.42/4.01      ( v1_tsep_1(X0,X1)
% 27.42/4.01      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 27.42/4.01      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ l1_pre_topc(X0)
% 27.42/4.01      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X0)
% 27.42/4.01      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 27.42/4.01      inference(cnf_transformation,[],[f92]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_873,plain,
% 27.42/4.01      ( v1_tsep_1(X0_54,X1_54)
% 27.42/4.01      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
% 27.42/4.01      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X0_54)
% 27.42/4.01      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)))
% 27.42/4.01      | ~ v2_pre_topc(X1_54)
% 27.42/4.01      | ~ v2_pre_topc(X0_54)
% 27.42/4.01      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_9]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1459,plain,
% 27.42/4.01      ( v1_tsep_1(X0_54,X1_54) = iProver_top
% 27.42/4.01      | v1_tsep_1(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) != iProver_top
% 27.42/4.01      | v2_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1638,plain,
% 27.42/4.01      ( v1_tsep_1(X0_54,X1_54) = iProver_top
% 27.42/4.01      | v1_tsep_1(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X1_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top ),
% 27.42/4.01      inference(forward_subsumption_resolution,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_1459,c_1455,c_1456]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9102,plain,
% 27.42/4.01      ( v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X0_54) != iProver_top
% 27.42/4.01      | v1_tsep_1(sK2,X0_54) = iProver_top
% 27.42/4.01      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK2) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK2) != iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_3188,c_1638]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9158,plain,
% 27.42/4.01      ( v1_tsep_1(sK2,X0_54) = iProver_top
% 27.42/4.01      | v1_tsep_1(sK3,X0_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK2) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK2) != iProver_top ),
% 27.42/4.01      inference(light_normalisation,[status(thm)],[c_9102,c_3188,c_3849]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1887,plain,
% 27.42/4.01      ( l1_pre_topc(sK0) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK0) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK2) = iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1470,c_1455]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9362,plain,
% 27.42/4.01      ( v2_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v1_tsep_1(sK2,X0_54) = iProver_top
% 27.42/4.01      | v1_tsep_1(sK3,X0_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_9158,c_40,c_41,c_1887,c_2378]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9363,plain,
% 27.42/4.01      ( v1_tsep_1(sK2,X0_54) = iProver_top
% 27.42/4.01      | v1_tsep_1(sK3,X0_54) != iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,X0_54) != iProver_top
% 27.42/4.01      | l1_pre_topc(X0_54) != iProver_top
% 27.42/4.01      | v2_pre_topc(X0_54) != iProver_top ),
% 27.42/4.01      inference(renaming,[status(thm)],[c_9362]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_9375,plain,
% 27.42/4.01      ( v1_tsep_1(sK2,sK3) = iProver_top
% 27.42/4.01      | v1_tsep_1(sK3,sK3) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK3) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK3) != iProver_top ),
% 27.42/4.01      inference(superposition,[status(thm)],[c_1461,c_9363]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_6,plain,
% 27.42/4.01      ( v3_pre_topc(k2_struct_0(X0),X0)
% 27.42/4.01      | ~ l1_pre_topc(X0)
% 27.42/4.01      | ~ v2_pre_topc(X0) ),
% 27.42/4.01      inference(cnf_transformation,[],[f58]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_13,plain,
% 27.42/4.01      ( v1_tsep_1(X0,X1)
% 27.42/4.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.01      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 27.42/4.01      | ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X1) ),
% 27.42/4.01      inference(cnf_transformation,[],[f96]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_15,plain,
% 27.42/4.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.01      | ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ l1_pre_topc(X1) ),
% 27.42/4.01      inference(cnf_transformation,[],[f67]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_209,plain,
% 27.42/4.01      ( v1_tsep_1(X0,X1)
% 27.42/4.01      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 27.42/4.01      | ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X1) ),
% 27.42/4.01      inference(global_propositional_subsumption,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_13,c_15]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_421,plain,
% 27.42/4.01      ( v1_tsep_1(X0,X1)
% 27.42/4.01      | ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ l1_pre_topc(X2)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X2)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | X1 != X2
% 27.42/4.01      | u1_struct_0(X0) != k2_struct_0(X2) ),
% 27.42/4.01      inference(resolution_lifted,[status(thm)],[c_6,c_209]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_422,plain,
% 27.42/4.01      ( v1_tsep_1(X0,X1)
% 27.42/4.01      | ~ m1_pre_topc(X0,X1)
% 27.42/4.01      | ~ l1_pre_topc(X1)
% 27.42/4.01      | ~ v2_pre_topc(X1)
% 27.42/4.01      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 27.42/4.01      inference(unflattening,[status(thm)],[c_421]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_848,plain,
% 27.42/4.01      ( v1_tsep_1(X0_54,X1_54)
% 27.42/4.01      | ~ m1_pre_topc(X0_54,X1_54)
% 27.42/4.01      | ~ l1_pre_topc(X1_54)
% 27.42/4.01      | ~ v2_pre_topc(X1_54)
% 27.42/4.01      | u1_struct_0(X0_54) != k2_struct_0(X1_54) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_422]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_3767,plain,
% 27.42/4.01      ( v1_tsep_1(sK3,X0_54)
% 27.42/4.01      | ~ m1_pre_topc(sK3,X0_54)
% 27.42/4.01      | ~ l1_pre_topc(X0_54)
% 27.42/4.01      | ~ v2_pre_topc(X0_54)
% 27.42/4.01      | u1_struct_0(sK3) != k2_struct_0(X0_54) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_848]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_5569,plain,
% 27.42/4.01      ( v1_tsep_1(sK3,sK3)
% 27.42/4.01      | ~ m1_pre_topc(sK3,sK3)
% 27.42/4.01      | ~ l1_pre_topc(sK3)
% 27.42/4.01      | ~ v2_pre_topc(sK3)
% 27.42/4.01      | u1_struct_0(sK3) != k2_struct_0(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_3767]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_5570,plain,
% 27.42/4.01      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 27.42/4.01      | v1_tsep_1(sK3,sK3) = iProver_top
% 27.42/4.01      | m1_pre_topc(sK3,sK3) != iProver_top
% 27.42/4.01      | l1_pre_topc(sK3) != iProver_top
% 27.42/4.01      | v2_pre_topc(sK3) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_5569]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1977,plain,
% 27.42/4.01      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_871]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1982,plain,
% 27.42/4.01      ( m1_pre_topc(sK3,sK3) = iProver_top
% 27.42/4.01      | l1_pre_topc(sK3) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_1977]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1948,plain,
% 27.42/4.01      ( ~ l1_pre_topc(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_849]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1950,plain,
% 27.42/4.01      ( u1_struct_0(sK3) = k2_struct_0(sK3)
% 27.42/4.01      | l1_pre_topc(sK3) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_880,plain,( X0_55 = X0_55 ),theory(equality) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1820,plain,
% 27.42/4.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_880]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_23,negated_conjecture,
% 27.42/4.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 27.42/4.01      inference(cnf_transformation,[],[f87]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_866,negated_conjecture,
% 27.42/4.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 27.42/4.01      inference(subtyping,[status(esa)],[c_23]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1465,plain,
% 27.42/4.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_1508,plain,
% 27.42/4.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 27.42/4.01      inference(light_normalisation,[status(thm)],[c_1465,c_867]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_879,plain,( X0_54 = X0_54 ),theory(equality) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_913,plain,
% 27.42/4.01      ( sK1 = sK1 ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_879]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_887,plain,
% 27.42/4.01      ( u1_struct_0(X0_54) = u1_struct_0(X1_54) | X0_54 != X1_54 ),
% 27.42/4.01      theory(equality) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_901,plain,
% 27.42/4.01      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 27.42/4.01      inference(instantiation,[status(thm)],[c_887]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_20,negated_conjecture,
% 27.42/4.01      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 27.42/4.01      inference(cnf_transformation,[],[f90]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_55,plain,
% 27.42/4.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_24,negated_conjecture,
% 27.42/4.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 27.42/4.01      inference(cnf_transformation,[],[f86]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_52,plain,
% 27.42/4.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_32,negated_conjecture,
% 27.42/4.01      ( ~ v2_struct_0(sK2) ),
% 27.42/4.01      inference(cnf_transformation,[],[f78]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(c_45,plain,
% 27.42/4.01      ( v2_struct_0(sK2) != iProver_top ),
% 27.42/4.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.42/4.01  
% 27.42/4.01  cnf(contradiction,plain,
% 27.42/4.01      ( $false ),
% 27.42/4.01      inference(minisat,
% 27.42/4.01                [status(thm)],
% 27.42/4.01                [c_127332,c_47275,c_9375,c_6063,c_5570,c_2378,c_2377,
% 27.42/4.01                 c_1982,c_1950,c_1883,c_1820,c_1508,c_913,c_901,c_55,
% 27.42/4.01                 c_52,c_51,c_47,c_45,c_44,c_43,c_42,c_41,c_40]) ).
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.42/4.01  
% 27.42/4.01  ------                               Statistics
% 27.42/4.01  
% 27.42/4.01  ------ General
% 27.42/4.01  
% 27.42/4.01  abstr_ref_over_cycles:                  0
% 27.42/4.01  abstr_ref_under_cycles:                 0
% 27.42/4.01  gc_basic_clause_elim:                   0
% 27.42/4.01  forced_gc_time:                         0
% 27.42/4.01  parsing_time:                           0.014
% 27.42/4.01  unif_index_cands_time:                  0.
% 27.42/4.01  unif_index_add_time:                    0.
% 27.42/4.01  orderings_time:                         0.
% 27.42/4.01  out_proof_time:                         0.021
% 27.42/4.01  total_time:                             3.124
% 27.42/4.01  num_of_symbols:                         60
% 27.42/4.01  num_of_terms:                           13885
% 27.42/4.01  
% 27.42/4.01  ------ Preprocessing
% 27.42/4.01  
% 27.42/4.01  num_of_splits:                          0
% 27.42/4.01  num_of_split_atoms:                     0
% 27.42/4.01  num_of_reused_defs:                     0
% 27.42/4.01  num_eq_ax_congr_red:                    9
% 27.42/4.01  num_of_sem_filtered_clauses:            1
% 27.42/4.01  num_of_subtypes:                        3
% 27.42/4.01  monotx_restored_types:                  0
% 27.42/4.01  sat_num_of_epr_types:                   0
% 27.42/4.01  sat_num_of_non_cyclic_types:            0
% 27.42/4.01  sat_guarded_non_collapsed_types:        0
% 27.42/4.01  num_pure_diseq_elim:                    0
% 27.42/4.01  simp_replaced_by:                       0
% 27.42/4.01  res_preprocessed:                       176
% 27.42/4.01  prep_upred:                             0
% 27.42/4.01  prep_unflattend:                        4
% 27.42/4.01  smt_new_axioms:                         0
% 27.42/4.01  pred_elim_cands:                        7
% 27.42/4.01  pred_elim:                              4
% 27.42/4.01  pred_elim_cl:                           5
% 27.42/4.01  pred_elim_cycles:                       6
% 27.42/4.01  merged_defs:                            0
% 27.42/4.01  merged_defs_ncl:                        0
% 27.42/4.01  bin_hyper_res:                          0
% 27.42/4.01  prep_cycles:                            4
% 27.42/4.01  pred_elim_time:                         0.01
% 27.42/4.01  splitting_time:                         0.
% 27.42/4.01  sem_filter_time:                        0.
% 27.42/4.01  monotx_time:                            0.
% 27.42/4.01  subtype_inf_time:                       0.001
% 27.42/4.01  
% 27.42/4.01  ------ Problem properties
% 27.42/4.01  
% 27.42/4.01  clauses:                                33
% 27.42/4.01  conjectures:                            17
% 27.42/4.01  epr:                                    16
% 27.42/4.01  horn:                                   30
% 27.42/4.01  ground:                                 17
% 27.42/4.01  unary:                                  17
% 27.42/4.01  binary:                                 2
% 27.42/4.01  lits:                                   128
% 27.42/4.01  lits_eq:                                11
% 27.42/4.01  fd_pure:                                0
% 27.42/4.01  fd_pseudo:                              0
% 27.42/4.01  fd_cond:                                0
% 27.42/4.01  fd_pseudo_cond:                         0
% 27.42/4.01  ac_symbols:                             0
% 27.42/4.01  
% 27.42/4.01  ------ Propositional Solver
% 27.42/4.01  
% 27.42/4.01  prop_solver_calls:                      34
% 27.42/4.01  prop_fast_solver_calls:                 6144
% 27.42/4.01  smt_solver_calls:                       0
% 27.42/4.01  smt_fast_solver_calls:                  0
% 27.42/4.01  prop_num_of_clauses:                    15714
% 27.42/4.01  prop_preprocess_simplified:             23703
% 27.42/4.01  prop_fo_subsumed:                       570
% 27.42/4.01  prop_solver_time:                       0.
% 27.42/4.01  smt_solver_time:                        0.
% 27.42/4.01  smt_fast_solver_time:                   0.
% 27.42/4.01  prop_fast_solver_time:                  0.
% 27.42/4.01  prop_unsat_core_time:                   0.001
% 27.42/4.01  
% 27.42/4.01  ------ QBF
% 27.42/4.01  
% 27.42/4.01  qbf_q_res:                              0
% 27.42/4.01  qbf_num_tautologies:                    0
% 27.42/4.01  qbf_prep_cycles:                        0
% 27.42/4.01  
% 27.42/4.01  ------ BMC1
% 27.42/4.01  
% 27.42/4.01  bmc1_current_bound:                     -1
% 27.42/4.01  bmc1_last_solved_bound:                 -1
% 27.42/4.01  bmc1_unsat_core_size:                   -1
% 27.42/4.01  bmc1_unsat_core_parents_size:           -1
% 27.42/4.01  bmc1_merge_next_fun:                    0
% 27.42/4.01  bmc1_unsat_core_clauses_time:           0.
% 27.42/4.01  
% 27.42/4.01  ------ Instantiation
% 27.42/4.01  
% 27.42/4.01  inst_num_of_clauses:                    3826
% 27.42/4.01  inst_num_in_passive:                    1195
% 27.42/4.01  inst_num_in_active:                     2393
% 27.42/4.01  inst_num_in_unprocessed:                238
% 27.42/4.01  inst_num_of_loops:                      2470
% 27.42/4.01  inst_num_of_learning_restarts:          0
% 27.42/4.01  inst_num_moves_active_passive:          67
% 27.42/4.01  inst_lit_activity:                      0
% 27.42/4.01  inst_lit_activity_moves:                0
% 27.42/4.01  inst_num_tautologies:                   0
% 27.42/4.01  inst_num_prop_implied:                  0
% 27.42/4.01  inst_num_existing_simplified:           0
% 27.42/4.01  inst_num_eq_res_simplified:             0
% 27.42/4.01  inst_num_child_elim:                    0
% 27.42/4.01  inst_num_of_dismatching_blockings:      6007
% 27.42/4.01  inst_num_of_non_proper_insts:           9547
% 27.42/4.01  inst_num_of_duplicates:                 0
% 27.42/4.01  inst_inst_num_from_inst_to_res:         0
% 27.42/4.01  inst_dismatching_checking_time:         0.
% 27.42/4.01  
% 27.42/4.01  ------ Resolution
% 27.42/4.01  
% 27.42/4.01  res_num_of_clauses:                     0
% 27.42/4.01  res_num_in_passive:                     0
% 27.42/4.01  res_num_in_active:                      0
% 27.42/4.01  res_num_of_loops:                       180
% 27.42/4.01  res_forward_subset_subsumed:            1187
% 27.42/4.01  res_backward_subset_subsumed:           14
% 27.42/4.01  res_forward_subsumed:                   0
% 27.42/4.01  res_backward_subsumed:                  0
% 27.42/4.01  res_forward_subsumption_resolution:     3
% 27.42/4.01  res_backward_subsumption_resolution:    0
% 27.42/4.01  res_clause_to_clause_subsumption:       116109
% 27.42/4.01  res_orphan_elimination:                 0
% 27.42/4.01  res_tautology_del:                      1469
% 27.42/4.01  res_num_eq_res_simplified:              0
% 27.42/4.01  res_num_sel_changes:                    0
% 27.42/4.01  res_moves_from_active_to_pass:          0
% 27.42/4.01  
% 27.42/4.01  ------ Superposition
% 27.42/4.01  
% 27.42/4.01  sup_time_total:                         0.
% 27.42/4.01  sup_time_generating:                    0.
% 27.42/4.01  sup_time_sim_full:                      0.
% 27.42/4.01  sup_time_sim_immed:                     0.
% 27.42/4.01  
% 27.42/4.01  sup_num_of_clauses:                     2290
% 27.42/4.01  sup_num_in_active:                      476
% 27.42/4.01  sup_num_in_passive:                     1814
% 27.42/4.01  sup_num_of_loops:                       492
% 27.42/4.01  sup_fw_superposition:                   6330
% 27.42/4.01  sup_bw_superposition:                   3062
% 27.42/4.01  sup_immediate_simplified:               6291
% 27.42/4.01  sup_given_eliminated:                   0
% 27.42/4.01  comparisons_done:                       0
% 27.42/4.01  comparisons_avoided:                    0
% 27.42/4.01  
% 27.42/4.01  ------ Simplifications
% 27.42/4.01  
% 27.42/4.01  
% 27.42/4.01  sim_fw_subset_subsumed:                 950
% 27.42/4.01  sim_bw_subset_subsumed:                 78
% 27.42/4.01  sim_fw_subsumed:                        4976
% 27.42/4.01  sim_bw_subsumed:                        133
% 27.42/4.01  sim_fw_subsumption_res:                 27
% 27.42/4.01  sim_bw_subsumption_res:                 6
% 27.42/4.01  sim_tautology_del:                      326
% 27.42/4.01  sim_eq_tautology_del:                   0
% 27.42/4.01  sim_eq_res_simp:                        0
% 27.42/4.01  sim_fw_demodulated:                     0
% 27.42/4.01  sim_bw_demodulated:                     14
% 27.42/4.01  sim_light_normalised:                   530
% 27.42/4.01  sim_joinable_taut:                      0
% 27.42/4.01  sim_joinable_simp:                      0
% 27.42/4.01  sim_ac_normalised:                      0
% 27.42/4.01  sim_smt_subsumption:                    0
% 27.42/4.01  
%------------------------------------------------------------------------------
