%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:32 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  240 (1493 expanded)
%              Number of clauses        :  147 ( 395 expanded)
%              Number of leaves         :   28 ( 601 expanded)
%              Depth                    :   25
%              Number of atoms          : 1230 (18605 expanded)
%              Number of equality atoms :  368 (2846 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f54,f53,f52,f51,f50,f49,f48])).

fof(f84,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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

fof(f76,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(equality_resolution,[],[f76])).

fof(f88,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f55])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2375,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2387,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4484,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_2387])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2915,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3114,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2915])).

cnf(c_3115,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3114])).

cnf(c_4855,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4484,c_42,c_47,c_3115])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_520,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_8])).

cnf(c_2365,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_4860,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4855,c_2365])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2377,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4483,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2377,c_2387])).

cnf(c_49,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2942,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3496,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_3497,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3496])).

cnf(c_4771,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4483,c_42,c_49,c_3497])).

cnf(c_4776,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_4771,c_2365])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2384,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5097,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_2384])).

cnf(c_7923,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4860,c_5097])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2381,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2438,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2381,c_23])).

cnf(c_14,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_560,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | X1 != X3
    | k2_struct_0(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_15])).

cnf(c_561,plain,
    ( m1_connsp_2(k2_struct_0(X0),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,k2_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_579,plain,
    ( m1_connsp_2(k2_struct_0(X0),X0,X1)
    | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,k2_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_561,c_6])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_725,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
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
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_726,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
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
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_730,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X5,X3,X4)
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
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_29])).

cnf(c_731,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
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
    inference(renaming,[status(thm)],[c_730])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_778,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_731,c_18])).

cnf(c_802,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k2_struct_0(X6),k1_zfmisc_1(u1_struct_0(X6)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X7,k2_struct_0(X6))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | X3 != X6
    | X4 != X7
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | k2_struct_0(X6) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_579,c_778])).

cnf(c_803,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_851,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_803,c_7,c_10,c_6])).

cnf(c_2364,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
    | r1_tarski(k2_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_3171,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2364])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_45,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3319,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3171,c_43,c_44,c_45])).

cnf(c_3320,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3319])).

cnf(c_3338,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3320])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1549,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2668,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_2857,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_2373,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3345,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2373,c_2365])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2378,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3656,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3345,c_2378])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3438,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
    | ~ r1_tarski(u1_struct_0(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3857,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3438])).

cnf(c_3859,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3857])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3858,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3861,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3858])).

cnf(c_3653,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3345,c_3320])).

cnf(c_4044,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3653])).

cnf(c_1555,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4831,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_4845,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_1550,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3000,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_4299,plain,
    ( X0 = u1_struct_0(sK3)
    | X0 != k2_struct_0(sK3)
    | u1_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3000])).

cnf(c_6137,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4299])).

cnf(c_1554,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2712,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1554])).

cnf(c_2877,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2712])).

cnf(c_3291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_struct_0(sK3) != X0
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2877])).

cnf(c_6414,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3291])).

cnf(c_6415,plain,
    ( k2_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6414])).

cnf(c_6965,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3338,c_37,c_48,c_30,c_2668,c_2857,c_3496,c_3656,c_3859,c_3861,c_4044,c_4831,c_4845,c_6137,c_6415])).

cnf(c_6966,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6965])).

cnf(c_6982,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_6966])).

cnf(c_6994,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6982,c_4860])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2385,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2386,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5606,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4860,c_2386])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5206,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4860,c_26])).

cnf(c_5638,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5606,c_5206])).

cnf(c_6046,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5638,c_42,c_47,c_3115])).

cnf(c_6047,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6046])).

cnf(c_6055,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_6047])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_211,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_10])).

cnf(c_212,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_2367,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_5376,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4860,c_2367])).

cnf(c_5402,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5376,c_5206])).

cnf(c_5882,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5402,c_42,c_47,c_3115])).

cnf(c_5883,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5882])).

cnf(c_5890,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_5883])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2380,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2421,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2380,c_23])).

cnf(c_5205,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4860,c_2421])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2379,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2392,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4590,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_2392])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2691,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r2_hidden(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2692,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2691])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_506,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_2772,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_2773,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2772])).

cnf(c_4862,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4590,c_42,c_48,c_49,c_53,c_2692,c_2773,c_3497])).

cnf(c_4949,plain,
    ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4776,c_4862])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_56,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_46,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_41,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_40,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7923,c_6994,c_6055,c_5890,c_5205,c_4949,c_3497,c_3115,c_56,c_49,c_47,c_46,c_42,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.31/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.00  
% 3.31/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.00  
% 3.31/1.00  ------  iProver source info
% 3.31/1.00  
% 3.31/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.00  git: non_committed_changes: false
% 3.31/1.00  git: last_make_outside_of_git: false
% 3.31/1.00  
% 3.31/1.00  ------ 
% 3.31/1.00  
% 3.31/1.00  ------ Input Options
% 3.31/1.00  
% 3.31/1.00  --out_options                           all
% 3.31/1.00  --tptp_safe_out                         true
% 3.31/1.00  --problem_path                          ""
% 3.31/1.00  --include_path                          ""
% 3.31/1.00  --clausifier                            res/vclausify_rel
% 3.31/1.00  --clausifier_options                    --mode clausify
% 3.31/1.00  --stdin                                 false
% 3.31/1.00  --stats_out                             all
% 3.31/1.00  
% 3.31/1.00  ------ General Options
% 3.31/1.00  
% 3.31/1.00  --fof                                   false
% 3.31/1.00  --time_out_real                         305.
% 3.31/1.00  --time_out_virtual                      -1.
% 3.31/1.00  --symbol_type_check                     false
% 3.31/1.00  --clausify_out                          false
% 3.31/1.00  --sig_cnt_out                           false
% 3.31/1.00  --trig_cnt_out                          false
% 3.31/1.00  --trig_cnt_out_tolerance                1.
% 3.31/1.00  --trig_cnt_out_sk_spl                   false
% 3.31/1.00  --abstr_cl_out                          false
% 3.31/1.00  
% 3.31/1.00  ------ Global Options
% 3.31/1.00  
% 3.31/1.00  --schedule                              default
% 3.31/1.00  --add_important_lit                     false
% 3.31/1.00  --prop_solver_per_cl                    1000
% 3.31/1.00  --min_unsat_core                        false
% 3.31/1.00  --soft_assumptions                      false
% 3.31/1.00  --soft_lemma_size                       3
% 3.31/1.00  --prop_impl_unit_size                   0
% 3.31/1.00  --prop_impl_unit                        []
% 3.31/1.00  --share_sel_clauses                     true
% 3.31/1.00  --reset_solvers                         false
% 3.31/1.00  --bc_imp_inh                            [conj_cone]
% 3.31/1.00  --conj_cone_tolerance                   3.
% 3.31/1.00  --extra_neg_conj                        none
% 3.31/1.00  --large_theory_mode                     true
% 3.31/1.00  --prolific_symb_bound                   200
% 3.31/1.00  --lt_threshold                          2000
% 3.31/1.00  --clause_weak_htbl                      true
% 3.31/1.00  --gc_record_bc_elim                     false
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing Options
% 3.31/1.00  
% 3.31/1.00  --preprocessing_flag                    true
% 3.31/1.00  --time_out_prep_mult                    0.1
% 3.31/1.00  --splitting_mode                        input
% 3.31/1.00  --splitting_grd                         true
% 3.31/1.00  --splitting_cvd                         false
% 3.31/1.00  --splitting_cvd_svl                     false
% 3.31/1.00  --splitting_nvd                         32
% 3.31/1.00  --sub_typing                            true
% 3.31/1.00  --prep_gs_sim                           true
% 3.31/1.00  --prep_unflatten                        true
% 3.31/1.00  --prep_res_sim                          true
% 3.31/1.00  --prep_upred                            true
% 3.31/1.00  --prep_sem_filter                       exhaustive
% 3.31/1.00  --prep_sem_filter_out                   false
% 3.31/1.00  --pred_elim                             true
% 3.31/1.00  --res_sim_input                         true
% 3.31/1.00  --eq_ax_congr_red                       true
% 3.31/1.00  --pure_diseq_elim                       true
% 3.31/1.00  --brand_transform                       false
% 3.31/1.00  --non_eq_to_eq                          false
% 3.31/1.00  --prep_def_merge                        true
% 3.31/1.00  --prep_def_merge_prop_impl              false
% 3.31/1.00  --prep_def_merge_mbd                    true
% 3.31/1.00  --prep_def_merge_tr_red                 false
% 3.31/1.00  --prep_def_merge_tr_cl                  false
% 3.31/1.00  --smt_preprocessing                     true
% 3.31/1.00  --smt_ac_axioms                         fast
% 3.31/1.00  --preprocessed_out                      false
% 3.31/1.00  --preprocessed_stats                    false
% 3.31/1.00  
% 3.31/1.00  ------ Abstraction refinement Options
% 3.31/1.00  
% 3.31/1.00  --abstr_ref                             []
% 3.31/1.00  --abstr_ref_prep                        false
% 3.31/1.00  --abstr_ref_until_sat                   false
% 3.31/1.00  --abstr_ref_sig_restrict                funpre
% 3.31/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.00  --abstr_ref_under                       []
% 3.31/1.00  
% 3.31/1.00  ------ SAT Options
% 3.31/1.00  
% 3.31/1.00  --sat_mode                              false
% 3.31/1.00  --sat_fm_restart_options                ""
% 3.31/1.00  --sat_gr_def                            false
% 3.31/1.00  --sat_epr_types                         true
% 3.31/1.00  --sat_non_cyclic_types                  false
% 3.31/1.00  --sat_finite_models                     false
% 3.31/1.00  --sat_fm_lemmas                         false
% 3.31/1.00  --sat_fm_prep                           false
% 3.31/1.00  --sat_fm_uc_incr                        true
% 3.31/1.00  --sat_out_model                         small
% 3.31/1.00  --sat_out_clauses                       false
% 3.31/1.00  
% 3.31/1.00  ------ QBF Options
% 3.31/1.00  
% 3.31/1.00  --qbf_mode                              false
% 3.31/1.00  --qbf_elim_univ                         false
% 3.31/1.00  --qbf_dom_inst                          none
% 3.31/1.00  --qbf_dom_pre_inst                      false
% 3.31/1.00  --qbf_sk_in                             false
% 3.31/1.00  --qbf_pred_elim                         true
% 3.31/1.00  --qbf_split                             512
% 3.31/1.00  
% 3.31/1.00  ------ BMC1 Options
% 3.31/1.00  
% 3.31/1.00  --bmc1_incremental                      false
% 3.31/1.00  --bmc1_axioms                           reachable_all
% 3.31/1.00  --bmc1_min_bound                        0
% 3.31/1.00  --bmc1_max_bound                        -1
% 3.31/1.00  --bmc1_max_bound_default                -1
% 3.31/1.00  --bmc1_symbol_reachability              true
% 3.31/1.00  --bmc1_property_lemmas                  false
% 3.31/1.00  --bmc1_k_induction                      false
% 3.31/1.00  --bmc1_non_equiv_states                 false
% 3.31/1.00  --bmc1_deadlock                         false
% 3.31/1.00  --bmc1_ucm                              false
% 3.31/1.00  --bmc1_add_unsat_core                   none
% 3.31/1.00  --bmc1_unsat_core_children              false
% 3.31/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.00  --bmc1_out_stat                         full
% 3.31/1.00  --bmc1_ground_init                      false
% 3.31/1.00  --bmc1_pre_inst_next_state              false
% 3.31/1.00  --bmc1_pre_inst_state                   false
% 3.31/1.00  --bmc1_pre_inst_reach_state             false
% 3.31/1.00  --bmc1_out_unsat_core                   false
% 3.31/1.00  --bmc1_aig_witness_out                  false
% 3.31/1.00  --bmc1_verbose                          false
% 3.31/1.00  --bmc1_dump_clauses_tptp                false
% 3.31/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.00  --bmc1_dump_file                        -
% 3.31/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.00  --bmc1_ucm_extend_mode                  1
% 3.31/1.00  --bmc1_ucm_init_mode                    2
% 3.31/1.00  --bmc1_ucm_cone_mode                    none
% 3.31/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.00  --bmc1_ucm_relax_model                  4
% 3.31/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.00  --bmc1_ucm_layered_model                none
% 3.31/1.00  --bmc1_ucm_max_lemma_size               10
% 3.31/1.00  
% 3.31/1.00  ------ AIG Options
% 3.31/1.00  
% 3.31/1.00  --aig_mode                              false
% 3.31/1.00  
% 3.31/1.00  ------ Instantiation Options
% 3.31/1.00  
% 3.31/1.00  --instantiation_flag                    true
% 3.31/1.00  --inst_sos_flag                         false
% 3.31/1.00  --inst_sos_phase                        true
% 3.31/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel_side                     num_symb
% 3.31/1.00  --inst_solver_per_active                1400
% 3.31/1.00  --inst_solver_calls_frac                1.
% 3.31/1.00  --inst_passive_queue_type               priority_queues
% 3.31/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.00  --inst_passive_queues_freq              [25;2]
% 3.31/1.00  --inst_dismatching                      true
% 3.31/1.00  --inst_eager_unprocessed_to_passive     true
% 3.31/1.00  --inst_prop_sim_given                   true
% 3.31/1.00  --inst_prop_sim_new                     false
% 3.31/1.00  --inst_subs_new                         false
% 3.31/1.00  --inst_eq_res_simp                      false
% 3.31/1.00  --inst_subs_given                       false
% 3.31/1.00  --inst_orphan_elimination               true
% 3.31/1.00  --inst_learning_loop_flag               true
% 3.31/1.00  --inst_learning_start                   3000
% 3.31/1.00  --inst_learning_factor                  2
% 3.31/1.00  --inst_start_prop_sim_after_learn       3
% 3.31/1.00  --inst_sel_renew                        solver
% 3.31/1.00  --inst_lit_activity_flag                true
% 3.31/1.00  --inst_restr_to_given                   false
% 3.31/1.00  --inst_activity_threshold               500
% 3.31/1.00  --inst_out_proof                        true
% 3.31/1.00  
% 3.31/1.00  ------ Resolution Options
% 3.31/1.00  
% 3.31/1.00  --resolution_flag                       true
% 3.31/1.00  --res_lit_sel                           adaptive
% 3.31/1.00  --res_lit_sel_side                      none
% 3.31/1.00  --res_ordering                          kbo
% 3.31/1.00  --res_to_prop_solver                    active
% 3.31/1.00  --res_prop_simpl_new                    false
% 3.31/1.00  --res_prop_simpl_given                  true
% 3.31/1.00  --res_passive_queue_type                priority_queues
% 3.31/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.00  --res_passive_queues_freq               [15;5]
% 3.31/1.00  --res_forward_subs                      full
% 3.31/1.00  --res_backward_subs                     full
% 3.31/1.00  --res_forward_subs_resolution           true
% 3.31/1.00  --res_backward_subs_resolution          true
% 3.31/1.00  --res_orphan_elimination                true
% 3.31/1.00  --res_time_limit                        2.
% 3.31/1.00  --res_out_proof                         true
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Options
% 3.31/1.00  
% 3.31/1.00  --superposition_flag                    true
% 3.31/1.00  --sup_passive_queue_type                priority_queues
% 3.31/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.00  --demod_completeness_check              fast
% 3.31/1.00  --demod_use_ground                      true
% 3.31/1.00  --sup_to_prop_solver                    passive
% 3.31/1.00  --sup_prop_simpl_new                    true
% 3.31/1.00  --sup_prop_simpl_given                  true
% 3.31/1.00  --sup_fun_splitting                     false
% 3.31/1.00  --sup_smt_interval                      50000
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Simplification Setup
% 3.31/1.00  
% 3.31/1.00  --sup_indices_passive                   []
% 3.31/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_full_bw                           [BwDemod]
% 3.31/1.00  --sup_immed_triv                        [TrivRules]
% 3.31/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_immed_bw_main                     []
% 3.31/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  
% 3.31/1.00  ------ Combination Options
% 3.31/1.00  
% 3.31/1.00  --comb_res_mult                         3
% 3.31/1.00  --comb_sup_mult                         2
% 3.31/1.00  --comb_inst_mult                        10
% 3.31/1.00  
% 3.31/1.00  ------ Debug Options
% 3.31/1.00  
% 3.31/1.00  --dbg_backtrace                         false
% 3.31/1.00  --dbg_dump_prop_clauses                 false
% 3.31/1.00  --dbg_dump_prop_clauses_file            -
% 3.31/1.00  --dbg_out_stat                          false
% 3.31/1.00  ------ Parsing...
% 3.31/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.00  ------ Proving...
% 3.31/1.00  ------ Problem Properties 
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  clauses                                 34
% 3.31/1.00  conjectures                             17
% 3.31/1.00  EPR                                     19
% 3.31/1.00  Horn                                    31
% 3.31/1.00  unary                                   18
% 3.31/1.00  binary                                  4
% 3.31/1.00  lits                                    98
% 3.31/1.00  lits eq                                 8
% 3.31/1.00  fd_pure                                 0
% 3.31/1.00  fd_pseudo                               0
% 3.31/1.00  fd_cond                                 0
% 3.31/1.00  fd_pseudo_cond                          1
% 3.31/1.00  AC symbols                              0
% 3.31/1.00  
% 3.31/1.00  ------ Schedule dynamic 5 is on 
% 3.31/1.00  
% 3.31/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  ------ 
% 3.31/1.00  Current options:
% 3.31/1.00  ------ 
% 3.31/1.00  
% 3.31/1.00  ------ Input Options
% 3.31/1.00  
% 3.31/1.00  --out_options                           all
% 3.31/1.00  --tptp_safe_out                         true
% 3.31/1.00  --problem_path                          ""
% 3.31/1.00  --include_path                          ""
% 3.31/1.00  --clausifier                            res/vclausify_rel
% 3.31/1.00  --clausifier_options                    --mode clausify
% 3.31/1.00  --stdin                                 false
% 3.31/1.00  --stats_out                             all
% 3.31/1.00  
% 3.31/1.00  ------ General Options
% 3.31/1.00  
% 3.31/1.00  --fof                                   false
% 3.31/1.00  --time_out_real                         305.
% 3.31/1.00  --time_out_virtual                      -1.
% 3.31/1.00  --symbol_type_check                     false
% 3.31/1.00  --clausify_out                          false
% 3.31/1.00  --sig_cnt_out                           false
% 3.31/1.00  --trig_cnt_out                          false
% 3.31/1.00  --trig_cnt_out_tolerance                1.
% 3.31/1.00  --trig_cnt_out_sk_spl                   false
% 3.31/1.00  --abstr_cl_out                          false
% 3.31/1.00  
% 3.31/1.00  ------ Global Options
% 3.31/1.00  
% 3.31/1.00  --schedule                              default
% 3.31/1.00  --add_important_lit                     false
% 3.31/1.00  --prop_solver_per_cl                    1000
% 3.31/1.00  --min_unsat_core                        false
% 3.31/1.00  --soft_assumptions                      false
% 3.31/1.00  --soft_lemma_size                       3
% 3.31/1.00  --prop_impl_unit_size                   0
% 3.31/1.00  --prop_impl_unit                        []
% 3.31/1.00  --share_sel_clauses                     true
% 3.31/1.00  --reset_solvers                         false
% 3.31/1.00  --bc_imp_inh                            [conj_cone]
% 3.31/1.00  --conj_cone_tolerance                   3.
% 3.31/1.00  --extra_neg_conj                        none
% 3.31/1.00  --large_theory_mode                     true
% 3.31/1.00  --prolific_symb_bound                   200
% 3.31/1.00  --lt_threshold                          2000
% 3.31/1.00  --clause_weak_htbl                      true
% 3.31/1.00  --gc_record_bc_elim                     false
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing Options
% 3.31/1.00  
% 3.31/1.00  --preprocessing_flag                    true
% 3.31/1.00  --time_out_prep_mult                    0.1
% 3.31/1.00  --splitting_mode                        input
% 3.31/1.00  --splitting_grd                         true
% 3.31/1.00  --splitting_cvd                         false
% 3.31/1.00  --splitting_cvd_svl                     false
% 3.31/1.00  --splitting_nvd                         32
% 3.31/1.00  --sub_typing                            true
% 3.31/1.00  --prep_gs_sim                           true
% 3.31/1.00  --prep_unflatten                        true
% 3.31/1.00  --prep_res_sim                          true
% 3.31/1.00  --prep_upred                            true
% 3.31/1.00  --prep_sem_filter                       exhaustive
% 3.31/1.00  --prep_sem_filter_out                   false
% 3.31/1.00  --pred_elim                             true
% 3.31/1.00  --res_sim_input                         true
% 3.31/1.00  --eq_ax_congr_red                       true
% 3.31/1.00  --pure_diseq_elim                       true
% 3.31/1.00  --brand_transform                       false
% 3.31/1.00  --non_eq_to_eq                          false
% 3.31/1.00  --prep_def_merge                        true
% 3.31/1.00  --prep_def_merge_prop_impl              false
% 3.31/1.00  --prep_def_merge_mbd                    true
% 3.31/1.00  --prep_def_merge_tr_red                 false
% 3.31/1.00  --prep_def_merge_tr_cl                  false
% 3.31/1.00  --smt_preprocessing                     true
% 3.31/1.00  --smt_ac_axioms                         fast
% 3.31/1.00  --preprocessed_out                      false
% 3.31/1.00  --preprocessed_stats                    false
% 3.31/1.00  
% 3.31/1.00  ------ Abstraction refinement Options
% 3.31/1.00  
% 3.31/1.00  --abstr_ref                             []
% 3.31/1.00  --abstr_ref_prep                        false
% 3.31/1.00  --abstr_ref_until_sat                   false
% 3.31/1.00  --abstr_ref_sig_restrict                funpre
% 3.31/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.00  --abstr_ref_under                       []
% 3.31/1.00  
% 3.31/1.00  ------ SAT Options
% 3.31/1.00  
% 3.31/1.00  --sat_mode                              false
% 3.31/1.00  --sat_fm_restart_options                ""
% 3.31/1.00  --sat_gr_def                            false
% 3.31/1.00  --sat_epr_types                         true
% 3.31/1.00  --sat_non_cyclic_types                  false
% 3.31/1.00  --sat_finite_models                     false
% 3.31/1.00  --sat_fm_lemmas                         false
% 3.31/1.00  --sat_fm_prep                           false
% 3.31/1.00  --sat_fm_uc_incr                        true
% 3.31/1.00  --sat_out_model                         small
% 3.31/1.00  --sat_out_clauses                       false
% 3.31/1.00  
% 3.31/1.00  ------ QBF Options
% 3.31/1.00  
% 3.31/1.00  --qbf_mode                              false
% 3.31/1.00  --qbf_elim_univ                         false
% 3.31/1.00  --qbf_dom_inst                          none
% 3.31/1.00  --qbf_dom_pre_inst                      false
% 3.31/1.00  --qbf_sk_in                             false
% 3.31/1.00  --qbf_pred_elim                         true
% 3.31/1.00  --qbf_split                             512
% 3.31/1.00  
% 3.31/1.00  ------ BMC1 Options
% 3.31/1.00  
% 3.31/1.00  --bmc1_incremental                      false
% 3.31/1.00  --bmc1_axioms                           reachable_all
% 3.31/1.00  --bmc1_min_bound                        0
% 3.31/1.00  --bmc1_max_bound                        -1
% 3.31/1.00  --bmc1_max_bound_default                -1
% 3.31/1.00  --bmc1_symbol_reachability              true
% 3.31/1.00  --bmc1_property_lemmas                  false
% 3.31/1.00  --bmc1_k_induction                      false
% 3.31/1.00  --bmc1_non_equiv_states                 false
% 3.31/1.00  --bmc1_deadlock                         false
% 3.31/1.00  --bmc1_ucm                              false
% 3.31/1.00  --bmc1_add_unsat_core                   none
% 3.31/1.00  --bmc1_unsat_core_children              false
% 3.31/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.00  --bmc1_out_stat                         full
% 3.31/1.00  --bmc1_ground_init                      false
% 3.31/1.00  --bmc1_pre_inst_next_state              false
% 3.31/1.00  --bmc1_pre_inst_state                   false
% 3.31/1.00  --bmc1_pre_inst_reach_state             false
% 3.31/1.00  --bmc1_out_unsat_core                   false
% 3.31/1.00  --bmc1_aig_witness_out                  false
% 3.31/1.00  --bmc1_verbose                          false
% 3.31/1.00  --bmc1_dump_clauses_tptp                false
% 3.31/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.00  --bmc1_dump_file                        -
% 3.31/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.00  --bmc1_ucm_extend_mode                  1
% 3.31/1.00  --bmc1_ucm_init_mode                    2
% 3.31/1.00  --bmc1_ucm_cone_mode                    none
% 3.31/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.00  --bmc1_ucm_relax_model                  4
% 3.31/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.00  --bmc1_ucm_layered_model                none
% 3.31/1.00  --bmc1_ucm_max_lemma_size               10
% 3.31/1.00  
% 3.31/1.00  ------ AIG Options
% 3.31/1.00  
% 3.31/1.00  --aig_mode                              false
% 3.31/1.00  
% 3.31/1.00  ------ Instantiation Options
% 3.31/1.00  
% 3.31/1.00  --instantiation_flag                    true
% 3.31/1.00  --inst_sos_flag                         false
% 3.31/1.00  --inst_sos_phase                        true
% 3.31/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel_side                     none
% 3.31/1.00  --inst_solver_per_active                1400
% 3.31/1.00  --inst_solver_calls_frac                1.
% 3.31/1.00  --inst_passive_queue_type               priority_queues
% 3.31/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.00  --inst_passive_queues_freq              [25;2]
% 3.31/1.00  --inst_dismatching                      true
% 3.31/1.00  --inst_eager_unprocessed_to_passive     true
% 3.31/1.00  --inst_prop_sim_given                   true
% 3.31/1.00  --inst_prop_sim_new                     false
% 3.31/1.00  --inst_subs_new                         false
% 3.31/1.00  --inst_eq_res_simp                      false
% 3.31/1.00  --inst_subs_given                       false
% 3.31/1.00  --inst_orphan_elimination               true
% 3.31/1.00  --inst_learning_loop_flag               true
% 3.31/1.00  --inst_learning_start                   3000
% 3.31/1.00  --inst_learning_factor                  2
% 3.31/1.00  --inst_start_prop_sim_after_learn       3
% 3.31/1.00  --inst_sel_renew                        solver
% 3.31/1.00  --inst_lit_activity_flag                true
% 3.31/1.00  --inst_restr_to_given                   false
% 3.31/1.00  --inst_activity_threshold               500
% 3.31/1.00  --inst_out_proof                        true
% 3.31/1.00  
% 3.31/1.00  ------ Resolution Options
% 3.31/1.00  
% 3.31/1.00  --resolution_flag                       false
% 3.31/1.00  --res_lit_sel                           adaptive
% 3.31/1.00  --res_lit_sel_side                      none
% 3.31/1.00  --res_ordering                          kbo
% 3.31/1.00  --res_to_prop_solver                    active
% 3.31/1.00  --res_prop_simpl_new                    false
% 3.31/1.00  --res_prop_simpl_given                  true
% 3.31/1.00  --res_passive_queue_type                priority_queues
% 3.31/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.00  --res_passive_queues_freq               [15;5]
% 3.31/1.00  --res_forward_subs                      full
% 3.31/1.00  --res_backward_subs                     full
% 3.31/1.00  --res_forward_subs_resolution           true
% 3.31/1.00  --res_backward_subs_resolution          true
% 3.31/1.00  --res_orphan_elimination                true
% 3.31/1.00  --res_time_limit                        2.
% 3.31/1.00  --res_out_proof                         true
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Options
% 3.31/1.00  
% 3.31/1.00  --superposition_flag                    true
% 3.31/1.00  --sup_passive_queue_type                priority_queues
% 3.31/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.00  --demod_completeness_check              fast
% 3.31/1.00  --demod_use_ground                      true
% 3.31/1.00  --sup_to_prop_solver                    passive
% 3.31/1.00  --sup_prop_simpl_new                    true
% 3.31/1.00  --sup_prop_simpl_given                  true
% 3.31/1.00  --sup_fun_splitting                     false
% 3.31/1.00  --sup_smt_interval                      50000
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Simplification Setup
% 3.31/1.00  
% 3.31/1.00  --sup_indices_passive                   []
% 3.31/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_full_bw                           [BwDemod]
% 3.31/1.00  --sup_immed_triv                        [TrivRules]
% 3.31/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_immed_bw_main                     []
% 3.31/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  
% 3.31/1.00  ------ Combination Options
% 3.31/1.00  
% 3.31/1.00  --comb_res_mult                         3
% 3.31/1.00  --comb_sup_mult                         2
% 3.31/1.00  --comb_inst_mult                        10
% 3.31/1.00  
% 3.31/1.00  ------ Debug Options
% 3.31/1.00  
% 3.31/1.00  --dbg_backtrace                         false
% 3.31/1.00  --dbg_dump_prop_clauses                 false
% 3.31/1.00  --dbg_dump_prop_clauses_file            -
% 3.31/1.00  --dbg_out_stat                          false
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  ------ Proving...
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  % SZS status Theorem for theBenchmark.p
% 3.31/1.00  
% 3.31/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/1.00  
% 3.31/1.00  fof(f17,conjecture,(
% 3.31/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f18,negated_conjecture,(
% 3.31/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.31/1.00    inference(negated_conjecture,[],[f17])).
% 3.31/1.00  
% 3.31/1.00  fof(f41,plain,(
% 3.31/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f18])).
% 3.31/1.00  
% 3.31/1.00  fof(f42,plain,(
% 3.31/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.31/1.00    inference(flattening,[],[f41])).
% 3.31/1.00  
% 3.31/1.00  fof(f54,plain,(
% 3.31/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f53,plain,(
% 3.31/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f52,plain,(
% 3.31/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f51,plain,(
% 3.31/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f50,plain,(
% 3.31/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f49,plain,(
% 3.31/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f48,plain,(
% 3.31/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f55,plain,(
% 3.31/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.31/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f54,f53,f52,f51,f50,f49,f48])).
% 3.31/1.00  
% 3.31/1.00  fof(f84,plain,(
% 3.31/1.00    m1_pre_topc(sK2,sK0)),
% 3.31/1.00    inference(cnf_transformation,[],[f55])).
% 3.31/1.00  
% 3.31/1.00  fof(f8,axiom,(
% 3.31/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f27,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f8])).
% 3.31/1.00  
% 3.31/1.00  fof(f66,plain,(
% 3.31/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f27])).
% 3.31/1.00  
% 3.31/1.00  fof(f79,plain,(
% 3.31/1.00    l1_pre_topc(sK0)),
% 3.31/1.00    inference(cnf_transformation,[],[f55])).
% 3.31/1.00  
% 3.31/1.00  fof(f7,axiom,(
% 3.31/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f26,plain,(
% 3.31/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f7])).
% 3.31/1.00  
% 3.31/1.00  fof(f65,plain,(
% 3.31/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f26])).
% 3.31/1.00  
% 3.31/1.00  fof(f6,axiom,(
% 3.31/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f25,plain,(
% 3.31/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f6])).
% 3.31/1.00  
% 3.31/1.00  fof(f64,plain,(
% 3.31/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f25])).
% 3.31/1.00  
% 3.31/1.00  fof(f86,plain,(
% 3.31/1.00    m1_pre_topc(sK3,sK0)),
% 3.31/1.00    inference(cnf_transformation,[],[f55])).
% 3.31/1.00  
% 3.31/1.00  fof(f14,axiom,(
% 3.31/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f36,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f14])).
% 3.31/1.00  
% 3.31/1.00  fof(f73,plain,(
% 3.31/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f36])).
% 3.31/1.00  
% 3.31/1.00  fof(f94,plain,(
% 3.31/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.31/1.00    inference(cnf_transformation,[],[f55])).
% 3.31/1.00  
% 3.31/1.00  fof(f93,plain,(
% 3.31/1.00    sK5 = sK6),
% 3.31/1.00    inference(cnf_transformation,[],[f55])).
% 3.31/1.00  
% 3.31/1.00  fof(f11,axiom,(
% 3.31/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f31,plain,(
% 3.31/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f11])).
% 3.31/1.00  
% 3.31/1.00  fof(f32,plain,(
% 3.31/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/1.00    inference(flattening,[],[f31])).
% 3.31/1.00  
% 3.31/1.00  fof(f70,plain,(
% 3.31/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f32])).
% 3.31/1.00  
% 3.31/1.00  fof(f12,axiom,(
% 3.31/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f33,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f12])).
% 3.31/1.00  
% 3.31/1.00  fof(f34,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.00    inference(flattening,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f71,plain,(
% 3.31/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f34])).
% 3.31/1.00  
% 3.31/1.00  fof(f4,axiom,(
% 3.31/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f21,plain,(
% 3.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.31/1.00    inference(ennf_transformation,[],[f4])).
% 3.31/1.00  
% 3.31/1.00  fof(f22,plain,(
% 3.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.31/1.00    inference(flattening,[],[f21])).
% 3.31/1.00  
% 3.31/1.00  fof(f62,plain,(
% 3.31/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f22])).
% 3.31/1.00  
% 3.31/1.00  fof(f16,axiom,(
% 3.31/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 3.31/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f39,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f16])).
% 3.31/1.00  
% 3.31/1.00  fof(f40,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.01    inference(flattening,[],[f39])).
% 3.31/1.01  
% 3.31/1.01  fof(f47,plain,(
% 3.31/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.01    inference(nnf_transformation,[],[f40])).
% 3.31/1.01  
% 3.31/1.01  fof(f76,plain,(
% 3.31/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f47])).
% 3.31/1.01  
% 3.31/1.01  fof(f98,plain,(
% 3.31/1.01    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.01    inference(equality_resolution,[],[f76])).
% 3.31/1.01  
% 3.31/1.01  fof(f88,plain,(
% 3.31/1.01    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f87,plain,(
% 3.31/1.01    v1_funct_1(sK4)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f15,axiom,(
% 3.31/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f37,plain,(
% 3.31/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/1.01    inference(ennf_transformation,[],[f15])).
% 3.31/1.01  
% 3.31/1.01  fof(f38,plain,(
% 3.31/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/1.01    inference(flattening,[],[f37])).
% 3.31/1.01  
% 3.31/1.01  fof(f74,plain,(
% 3.31/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f38])).
% 3.31/1.01  
% 3.31/1.01  fof(f5,axiom,(
% 3.31/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f23,plain,(
% 3.31/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/1.01    inference(ennf_transformation,[],[f5])).
% 3.31/1.01  
% 3.31/1.01  fof(f24,plain,(
% 3.31/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/1.01    inference(flattening,[],[f23])).
% 3.31/1.01  
% 3.31/1.01  fof(f63,plain,(
% 3.31/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f24])).
% 3.31/1.01  
% 3.31/1.01  fof(f80,plain,(
% 3.31/1.01    ~v2_struct_0(sK1)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f81,plain,(
% 3.31/1.01    v2_pre_topc(sK1)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f82,plain,(
% 3.31/1.01    l1_pre_topc(sK1)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f85,plain,(
% 3.31/1.01    ~v2_struct_0(sK3)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f89,plain,(
% 3.31/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f3,axiom,(
% 3.31/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f45,plain,(
% 3.31/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.31/1.01    inference(nnf_transformation,[],[f3])).
% 3.31/1.01  
% 3.31/1.01  fof(f61,plain,(
% 3.31/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f45])).
% 3.31/1.01  
% 3.31/1.01  fof(f1,axiom,(
% 3.31/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f43,plain,(
% 3.31/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.01    inference(nnf_transformation,[],[f1])).
% 3.31/1.01  
% 3.31/1.01  fof(f44,plain,(
% 3.31/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.01    inference(flattening,[],[f43])).
% 3.31/1.01  
% 3.31/1.01  fof(f57,plain,(
% 3.31/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.31/1.01    inference(cnf_transformation,[],[f44])).
% 3.31/1.01  
% 3.31/1.01  fof(f96,plain,(
% 3.31/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.31/1.01    inference(equality_resolution,[],[f57])).
% 3.31/1.01  
% 3.31/1.01  fof(f13,axiom,(
% 3.31/1.01    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f35,plain,(
% 3.31/1.01    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.31/1.01    inference(ennf_transformation,[],[f13])).
% 3.31/1.01  
% 3.31/1.01  fof(f72,plain,(
% 3.31/1.01    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f35])).
% 3.31/1.01  
% 3.31/1.01  fof(f10,axiom,(
% 3.31/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f30,plain,(
% 3.31/1.01    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.31/1.01    inference(ennf_transformation,[],[f10])).
% 3.31/1.01  
% 3.31/1.01  fof(f46,plain,(
% 3.31/1.01    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.31/1.01    inference(nnf_transformation,[],[f30])).
% 3.31/1.01  
% 3.31/1.01  fof(f69,plain,(
% 3.31/1.01    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f46])).
% 3.31/1.01  
% 3.31/1.01  fof(f90,plain,(
% 3.31/1.01    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f68,plain,(
% 3.31/1.01    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f46])).
% 3.31/1.01  
% 3.31/1.01  fof(f92,plain,(
% 3.31/1.01    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f91,plain,(
% 3.31/1.01    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f2,axiom,(
% 3.31/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f19,plain,(
% 3.31/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.31/1.01    inference(ennf_transformation,[],[f2])).
% 3.31/1.01  
% 3.31/1.01  fof(f20,plain,(
% 3.31/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.31/1.01    inference(flattening,[],[f19])).
% 3.31/1.01  
% 3.31/1.01  fof(f59,plain,(
% 3.31/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f20])).
% 3.31/1.01  
% 3.31/1.01  fof(f9,axiom,(
% 3.31/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.31/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/1.01  
% 3.31/1.01  fof(f28,plain,(
% 3.31/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.31/1.01    inference(ennf_transformation,[],[f9])).
% 3.31/1.01  
% 3.31/1.01  fof(f29,plain,(
% 3.31/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.31/1.01    inference(flattening,[],[f28])).
% 3.31/1.01  
% 3.31/1.01  fof(f67,plain,(
% 3.31/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.31/1.01    inference(cnf_transformation,[],[f29])).
% 3.31/1.01  
% 3.31/1.01  fof(f95,plain,(
% 3.31/1.01    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f83,plain,(
% 3.31/1.01    ~v2_struct_0(sK2)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f78,plain,(
% 3.31/1.01    v2_pre_topc(sK0)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  fof(f77,plain,(
% 3.31/1.01    ~v2_struct_0(sK0)),
% 3.31/1.01    inference(cnf_transformation,[],[f55])).
% 3.31/1.01  
% 3.31/1.01  cnf(c_32,negated_conjecture,
% 3.31/1.01      ( m1_pre_topc(sK2,sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2375,plain,
% 3.31/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_10,plain,
% 3.31/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2387,plain,
% 3.31/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top
% 3.31/1.01      | l1_pre_topc(X0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4484,plain,
% 3.31/1.01      ( l1_pre_topc(sK0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2375,c_2387]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_37,negated_conjecture,
% 3.31/1.01      ( l1_pre_topc(sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_42,plain,
% 3.31/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_47,plain,
% 3.31/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2915,plain,
% 3.31/1.01      ( ~ m1_pre_topc(sK2,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK2) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3114,plain,
% 3.31/1.01      ( ~ m1_pre_topc(sK2,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2915]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3115,plain,
% 3.31/1.01      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_3114]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4855,plain,
% 3.31/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_4484,c_42,c_47,c_3115]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_9,plain,
% 3.31/1.01      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_8,plain,
% 3.31/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_520,plain,
% 3.31/1.01      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.31/1.01      inference(resolution,[status(thm)],[c_9,c_8]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2365,plain,
% 3.31/1.01      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4860,plain,
% 3.31/1.01      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_4855,c_2365]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_30,negated_conjecture,
% 3.31/1.01      ( m1_pre_topc(sK3,sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2377,plain,
% 3.31/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4483,plain,
% 3.31/1.01      ( l1_pre_topc(sK0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK3) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2377,c_2387]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_49,plain,
% 3.31/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2942,plain,
% 3.31/1.01      ( ~ m1_pre_topc(sK3,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3496,plain,
% 3.31/1.01      ( ~ m1_pre_topc(sK3,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2942]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3497,plain,
% 3.31/1.01      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK3) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_3496]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4771,plain,
% 3.31/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_4483,c_42,c_49,c_3497]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4776,plain,
% 3.31/1.01      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_4771,c_2365]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_17,plain,
% 3.31/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2384,plain,
% 3.31/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5097,plain,
% 3.31/1.01      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_4776,c_2384]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7923,plain,
% 3.31/1.01      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_4860,c_5097]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_22,negated_conjecture,
% 3.31/1.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.31/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2381,plain,
% 3.31/1.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_23,negated_conjecture,
% 3.31/1.01      ( sK5 = sK6 ),
% 3.31/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2438,plain,
% 3.31/1.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.31/1.01      inference(light_normalisation,[status(thm)],[c_2381,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_14,plain,
% 3.31/1.01      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.31/1.01      | ~ l1_pre_topc(X0)
% 3.31/1.01      | ~ v2_pre_topc(X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_15,plain,
% 3.31/1.01      ( m1_connsp_2(X0,X1,X2)
% 3.31/1.01      | ~ v3_pre_topc(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ r2_hidden(X2,X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_560,plain,
% 3.31/1.01      ( m1_connsp_2(X0,X1,X2)
% 3.31/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ r2_hidden(X2,X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | ~ l1_pre_topc(X3)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X3)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | X1 != X3
% 3.31/1.01      | k2_struct_0(X3) != X0 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_15]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_561,plain,
% 3.31/1.01      ( m1_connsp_2(k2_struct_0(X0),X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.31/1.01      | ~ r2_hidden(X1,k2_struct_0(X0))
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | ~ l1_pre_topc(X0)
% 3.31/1.01      | ~ v2_pre_topc(X0) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_560]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6,plain,
% 3.31/1.01      ( m1_subset_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.31/1.01      | ~ r2_hidden(X0,X2) ),
% 3.31/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_579,plain,
% 3.31/1.01      ( m1_connsp_2(k2_struct_0(X0),X0,X1)
% 3.31/1.01      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.31/1.01      | ~ r2_hidden(X1,k2_struct_0(X0))
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | ~ l1_pre_topc(X0)
% 3.31/1.01      | ~ v2_pre_topc(X0) ),
% 3.31/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_561,c_6]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_19,plain,
% 3.31/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.31/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.01      | ~ m1_connsp_2(X6,X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X4,X5)
% 3.31/1.01      | ~ m1_pre_topc(X4,X0)
% 3.31/1.01      | ~ m1_pre_topc(X0,X5)
% 3.31/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.01      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.31/1.01      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.31/1.01      | ~ v1_funct_1(X2)
% 3.31/1.01      | v2_struct_0(X5)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X4)
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | ~ l1_pre_topc(X5)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X5)
% 3.31/1.01      | ~ v2_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_28,negated_conjecture,
% 3.31/1.01      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.31/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_725,plain,
% 3.31/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.31/1.01      | ~ m1_connsp_2(X6,X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X4,X5)
% 3.31/1.01      | ~ m1_pre_topc(X4,X0)
% 3.31/1.01      | ~ m1_pre_topc(X0,X5)
% 3.31/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.01      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.31/1.01      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.31/1.01      | ~ v1_funct_1(X2)
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X5)
% 3.31/1.01      | v2_struct_0(X4)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X5)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X5)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.31/1.01      | sK4 != X2 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_726,plain,
% 3.31/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/1.01      | ~ m1_connsp_2(X5,X3,X4)
% 3.31/1.01      | ~ m1_pre_topc(X0,X2)
% 3.31/1.01      | ~ m1_pre_topc(X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X3,X2)
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.31/1.01      | ~ v1_funct_1(sK4)
% 3.31/1.01      | v2_struct_0(X3)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X2)
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X2)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X2)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_725]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_29,negated_conjecture,
% 3.31/1.01      ( v1_funct_1(sK4) ),
% 3.31/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_730,plain,
% 3.31/1.01      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_pre_topc(X3,X2)
% 3.31/1.01      | ~ m1_pre_topc(X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X0,X2)
% 3.31/1.01      | ~ m1_connsp_2(X5,X3,X4)
% 3.31/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/1.01      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/1.01      | v2_struct_0(X3)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X2)
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X2)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X2)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_726,c_29]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_731,plain,
% 3.31/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/1.01      | ~ m1_connsp_2(X5,X3,X4)
% 3.31/1.01      | ~ m1_pre_topc(X0,X2)
% 3.31/1.01      | ~ m1_pre_topc(X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X3,X2)
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X2)
% 3.31/1.01      | v2_struct_0(X3)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X2)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X2)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_730]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_18,plain,
% 3.31/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.01      | ~ m1_pre_topc(X2,X0)
% 3.31/1.01      | m1_pre_topc(X2,X1)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_778,plain,
% 3.31/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/1.01      | ~ m1_connsp_2(X5,X3,X4)
% 3.31/1.01      | ~ m1_pre_topc(X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X3,X2)
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X2)
% 3.31/1.01      | v2_struct_0(X3)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X2)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X2)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/1.01      inference(forward_subsumption_resolution,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_731,c_18]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_802,plain,
% 3.31/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/1.01      | ~ m1_pre_topc(X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X3,X2)
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.01      | ~ m1_subset_1(k2_struct_0(X6),k1_zfmisc_1(u1_struct_0(X6)))
% 3.31/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/1.01      | ~ r2_hidden(X7,k2_struct_0(X6))
% 3.31/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.31/1.01      | v2_struct_0(X6)
% 3.31/1.01      | v2_struct_0(X3)
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X2)
% 3.31/1.01      | ~ l1_pre_topc(X6)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X2)
% 3.31/1.01      | ~ v2_pre_topc(X6)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X2)
% 3.31/1.01      | X3 != X6
% 3.31/1.01      | X4 != X7
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X3) != u1_struct_0(sK3)
% 3.31/1.01      | k2_struct_0(X6) != X5 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_579,c_778]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_803,plain,
% 3.31/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/1.01      | ~ m1_pre_topc(X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X3,X2)
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/1.01      | ~ r2_hidden(X4,k2_struct_0(X3))
% 3.31/1.01      | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X2)
% 3.31/1.01      | v2_struct_0(X3)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X2)
% 3.31/1.01      | ~ l1_pre_topc(X3)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X2)
% 3.31/1.01      | ~ v2_pre_topc(X3)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_802]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7,plain,
% 3.31/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | v2_pre_topc(X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_851,plain,
% 3.31/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.31/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.31/1.01      | ~ m1_pre_topc(X0,X3)
% 3.31/1.01      | ~ m1_pre_topc(X3,X2)
% 3.31/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.31/1.01      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.31/1.01      | ~ r2_hidden(X4,k2_struct_0(X3))
% 3.31/1.01      | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
% 3.31/1.01      | v2_struct_0(X0)
% 3.31/1.01      | v2_struct_0(X1)
% 3.31/1.01      | v2_struct_0(X2)
% 3.31/1.01      | v2_struct_0(X3)
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | ~ l1_pre_topc(X2)
% 3.31/1.01      | ~ v2_pre_topc(X1)
% 3.31/1.01      | ~ v2_pre_topc(X2)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.31/1.01      inference(forward_subsumption_resolution,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_803,c_7,c_10,c_6]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2364,plain,
% 3.31/1.01      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.31/1.01      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.31/1.01      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
% 3.31/1.01      | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
% 3.31/1.01      | m1_pre_topc(X2,X1) != iProver_top
% 3.31/1.01      | m1_pre_topc(X1,X3) != iProver_top
% 3.31/1.01      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.31/1.01      | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(X2) = iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | v2_struct_0(X3) = iProver_top
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top
% 3.31/1.01      | l1_pre_topc(X3) != iProver_top
% 3.31/1.01      | v2_pre_topc(X0) != iProver_top
% 3.31/1.01      | v2_pre_topc(X3) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3171,plain,
% 3.31/1.01      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.31/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.31/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.31/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(X2) = iProver_top
% 3.31/1.01      | v2_struct_0(sK1) = iProver_top
% 3.31/1.01      | l1_pre_topc(X2) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK1) != iProver_top
% 3.31/1.01      | v2_pre_topc(X2) != iProver_top
% 3.31/1.01      | v2_pre_topc(sK1) != iProver_top ),
% 3.31/1.01      inference(equality_resolution,[status(thm)],[c_2364]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_36,negated_conjecture,
% 3.31/1.01      ( ~ v2_struct_0(sK1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_43,plain,
% 3.31/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_35,negated_conjecture,
% 3.31/1.01      ( v2_pre_topc(sK1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_44,plain,
% 3.31/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_34,negated_conjecture,
% 3.31/1.01      ( l1_pre_topc(sK1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_45,plain,
% 3.31/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3319,plain,
% 3.31/1.01      ( v2_pre_topc(X2) != iProver_top
% 3.31/1.01      | v2_struct_0(X2) = iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.31/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.31/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.31/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.31/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.31/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.31/1.01      | l1_pre_topc(X2) != iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_3171,c_43,c_44,c_45]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3320,plain,
% 3.31/1.01      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.31/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.31/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.31/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(X2) = iProver_top
% 3.31/1.01      | l1_pre_topc(X2) != iProver_top
% 3.31/1.01      | v2_pre_topc(X2) != iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_3319]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3338,plain,
% 3.31/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.31/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.31/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.31/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(sK3) = iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top
% 3.31/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.31/1.01      inference(equality_resolution,[status(thm)],[c_3320]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_31,negated_conjecture,
% 3.31/1.01      ( ~ v2_struct_0(sK3) ),
% 3.31/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_48,plain,
% 3.31/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1549,plain,( X0 = X0 ),theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2668,plain,
% 3.31/1.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_1549]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2857,plain,
% 3.31/1.01      ( ~ l1_pre_topc(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_520]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2373,plain,
% 3.31/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3345,plain,
% 3.31/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2373,c_2365]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_27,negated_conjecture,
% 3.31/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.31/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2378,plain,
% 3.31/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3656,plain,
% 3.31/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_3345,c_2378]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3438,plain,
% 3.31/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
% 3.31/1.01      | ~ r1_tarski(u1_struct_0(sK3),X0) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3857,plain,
% 3.31/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.31/1.01      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_3438]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3859,plain,
% 3.31/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.31/1.01      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_3857]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1,plain,
% 3.31/1.01      ( r1_tarski(X0,X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3858,plain,
% 3.31/1.01      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3861,plain,
% 3.31/1.01      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_3858]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3653,plain,
% 3.31/1.01      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.31/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.31/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.31/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.31/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
% 3.31/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(X2) = iProver_top
% 3.31/1.01      | l1_pre_topc(X2) != iProver_top
% 3.31/1.01      | v2_pre_topc(X2) != iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_3345,c_3320]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4044,plain,
% 3.31/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.31/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.31/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.31/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.31/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(sK3) = iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top
% 3.31/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.31/1.01      inference(equality_resolution,[status(thm)],[c_3653]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1555,plain,
% 3.31/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.31/1.01      theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4831,plain,
% 3.31/1.01      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.31/1.01      | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_1555]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4845,plain,
% 3.31/1.01      ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_1549]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1550,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3000,plain,
% 3.31/1.01      ( X0 != X1 | X0 = u1_struct_0(sK3) | u1_struct_0(sK3) != X1 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_1550]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4299,plain,
% 3.31/1.01      ( X0 = u1_struct_0(sK3)
% 3.31/1.01      | X0 != k2_struct_0(sK3)
% 3.31/1.01      | u1_struct_0(sK3) != k2_struct_0(sK3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_3000]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6137,plain,
% 3.31/1.01      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 3.31/1.01      | k2_struct_0(sK3) = u1_struct_0(sK3)
% 3.31/1.01      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_4299]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1554,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.31/1.01      theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2712,plain,
% 3.31/1.01      ( m1_subset_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.31/1.01      | X0 != X2
% 3.31/1.01      | X1 != k1_zfmisc_1(X3) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_1554]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2877,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.31/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.31/1.01      | X2 != X0
% 3.31/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2712]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3291,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.31/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.31/1.01      | k2_struct_0(sK3) != X0
% 3.31/1.01      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2877]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6414,plain,
% 3.31/1.01      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.31/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.31/1.01      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 3.31/1.01      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_3291]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6415,plain,
% 3.31/1.01      ( k2_struct_0(sK3) != u1_struct_0(sK3)
% 3.31/1.01      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.31/1.01      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_6414]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6965,plain,
% 3.31/1.01      ( v2_struct_0(X0) = iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.31/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.31/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.31/1.01      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top
% 3.31/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_3338,c_37,c_48,c_30,c_2668,c_2857,c_3496,c_3656,
% 3.31/1.01                 c_3859,c_3861,c_4044,c_4831,c_4845,c_6137,c_6415]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6966,plain,
% 3.31/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.31/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.31/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.31/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.31/1.01      | v2_struct_0(X1) = iProver_top
% 3.31/1.01      | v2_struct_0(X0) = iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top
% 3.31/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_6965]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6982,plain,
% 3.31/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.31/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.31/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.31/1.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.31/1.01      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.31/1.01      | v2_struct_0(sK0) = iProver_top
% 3.31/1.01      | v2_struct_0(sK2) = iProver_top
% 3.31/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.31/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2438,c_6966]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6994,plain,
% 3.31/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.31/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.31/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.31/1.01      | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
% 3.31/1.01      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 3.31/1.01      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
% 3.31/1.01      | v2_struct_0(sK0) = iProver_top
% 3.31/1.01      | v2_struct_0(sK2) = iProver_top
% 3.31/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.31/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.31/1.01      inference(light_normalisation,[status(thm)],[c_6982,c_4860]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_16,plain,
% 3.31/1.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2385,plain,
% 3.31/1.01      ( m1_pre_topc(X0,X0) = iProver_top
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_12,plain,
% 3.31/1.01      ( m1_pre_topc(X0,X1)
% 3.31/1.01      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.31/1.01      | ~ l1_pre_topc(X0)
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2386,plain,
% 3.31/1.01      ( m1_pre_topc(X0,X1) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5606,plain,
% 3.31/1.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK2) = iProver_top
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_4860,c_2386]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_26,negated_conjecture,
% 3.31/1.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.31/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5206,plain,
% 3.31/1.01      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_4860,c_26]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5638,plain,
% 3.31/1.01      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.01      inference(light_normalisation,[status(thm)],[c_5606,c_5206]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6046,plain,
% 3.31/1.01      ( l1_pre_topc(X0) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_5638,c_42,c_47,c_3115]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6047,plain,
% 3.31/1.01      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.31/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_6046]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6055,plain,
% 3.31/1.01      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.31/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2385,c_6047]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_13,plain,
% 3.31/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.31/1.01      | ~ l1_pre_topc(X0)
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_211,plain,
% 3.31/1.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.31/1.01      | ~ m1_pre_topc(X0,X1)
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_13,c_10]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_212,plain,
% 3.31/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_211]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2367,plain,
% 3.31/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.31/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5376,plain,
% 3.31/1.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK2) != iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_4860,c_2367]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5402,plain,
% 3.31/1.01      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) = iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.01      inference(light_normalisation,[status(thm)],[c_5376,c_5206]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5882,plain,
% 3.31/1.01      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_5402,c_42,c_47,c_3115]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5883,plain,
% 3.31/1.01      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.31/1.01      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_5882]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5890,plain,
% 3.31/1.01      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.31/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2385,c_5883]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_24,negated_conjecture,
% 3.31/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.31/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2380,plain,
% 3.31/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2421,plain,
% 3.31/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.31/1.01      inference(light_normalisation,[status(thm)],[c_2380,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5205,plain,
% 3.31/1.01      ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_4860,c_2421]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_25,negated_conjecture,
% 3.31/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.31/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2379,plain,
% 3.31/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2392,plain,
% 3.31/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.31/1.01      | r2_hidden(X0,X1) = iProver_top
% 3.31/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4590,plain,
% 3.31/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.31/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_2379,c_2392]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_53,plain,
% 3.31/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2691,plain,
% 3.31/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.31/1.01      | r2_hidden(sK5,u1_struct_0(sK3))
% 3.31/1.01      | v1_xboole_0(u1_struct_0(sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2692,plain,
% 3.31/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.31/1.01      | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.31/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2691]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_11,plain,
% 3.31/1.01      ( v2_struct_0(X0)
% 3.31/1.01      | ~ l1_struct_0(X0)
% 3.31/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.31/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_506,plain,
% 3.31/1.01      ( v2_struct_0(X0)
% 3.31/1.01      | ~ l1_pre_topc(X0)
% 3.31/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.31/1.01      inference(resolution,[status(thm)],[c_9,c_11]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2772,plain,
% 3.31/1.01      ( v2_struct_0(sK3)
% 3.31/1.01      | ~ l1_pre_topc(sK3)
% 3.31/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_506]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2773,plain,
% 3.31/1.01      ( v2_struct_0(sK3) = iProver_top
% 3.31/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.31/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_2772]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4862,plain,
% 3.31/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_4590,c_42,c_48,c_49,c_53,c_2692,c_2773,c_3497]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4949,plain,
% 3.31/1.01      ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_4776,c_4862]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_21,negated_conjecture,
% 3.31/1.01      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.31/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_56,plain,
% 3.31/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_33,negated_conjecture,
% 3.31/1.01      ( ~ v2_struct_0(sK2) ),
% 3.31/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_46,plain,
% 3.31/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_38,negated_conjecture,
% 3.31/1.01      ( v2_pre_topc(sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_41,plain,
% 3.31/1.01      ( v2_pre_topc(sK0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_39,negated_conjecture,
% 3.31/1.01      ( ~ v2_struct_0(sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_40,plain,
% 3.31/1.01      ( v2_struct_0(sK0) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(contradiction,plain,
% 3.31/1.01      ( $false ),
% 3.31/1.01      inference(minisat,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_7923,c_6994,c_6055,c_5890,c_5205,c_4949,c_3497,c_3115,
% 3.31/1.01                 c_56,c_49,c_47,c_46,c_42,c_41,c_40]) ).
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/1.01  
% 3.31/1.01  ------                               Statistics
% 3.31/1.01  
% 3.31/1.01  ------ General
% 3.31/1.01  
% 3.31/1.01  abstr_ref_over_cycles:                  0
% 3.31/1.01  abstr_ref_under_cycles:                 0
% 3.31/1.01  gc_basic_clause_elim:                   0
% 3.31/1.01  forced_gc_time:                         0
% 3.31/1.01  parsing_time:                           0.009
% 3.31/1.01  unif_index_cands_time:                  0.
% 3.31/1.01  unif_index_add_time:                    0.
% 3.31/1.01  orderings_time:                         0.
% 3.31/1.01  out_proof_time:                         0.017
% 3.31/1.01  total_time:                             0.254
% 3.31/1.01  num_of_symbols:                         59
% 3.31/1.01  num_of_terms:                           4262
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing
% 3.31/1.01  
% 3.31/1.01  num_of_splits:                          0
% 3.31/1.01  num_of_split_atoms:                     0
% 3.31/1.01  num_of_reused_defs:                     0
% 3.31/1.01  num_eq_ax_congr_red:                    12
% 3.31/1.01  num_of_sem_filtered_clauses:            1
% 3.31/1.01  num_of_subtypes:                        0
% 3.31/1.01  monotx_restored_types:                  0
% 3.31/1.01  sat_num_of_epr_types:                   0
% 3.31/1.01  sat_num_of_non_cyclic_types:            0
% 3.31/1.01  sat_guarded_non_collapsed_types:        0
% 3.31/1.01  num_pure_diseq_elim:                    0
% 3.31/1.01  simp_replaced_by:                       0
% 3.31/1.01  res_preprocessed:                       176
% 3.31/1.01  prep_upred:                             0
% 3.31/1.01  prep_unflattend:                        29
% 3.31/1.01  smt_new_axioms:                         0
% 3.31/1.01  pred_elim_cands:                        9
% 3.31/1.01  pred_elim:                              5
% 3.31/1.01  pred_elim_cl:                           5
% 3.31/1.01  pred_elim_cycles:                       11
% 3.31/1.01  merged_defs:                            8
% 3.31/1.01  merged_defs_ncl:                        0
% 3.31/1.01  bin_hyper_res:                          8
% 3.31/1.01  prep_cycles:                            4
% 3.31/1.01  pred_elim_time:                         0.031
% 3.31/1.01  splitting_time:                         0.
% 3.31/1.01  sem_filter_time:                        0.
% 3.31/1.01  monotx_time:                            0.
% 3.31/1.01  subtype_inf_time:                       0.
% 3.31/1.01  
% 3.31/1.01  ------ Problem properties
% 3.31/1.01  
% 3.31/1.01  clauses:                                34
% 3.31/1.01  conjectures:                            17
% 3.31/1.01  epr:                                    19
% 3.31/1.01  horn:                                   31
% 3.31/1.01  ground:                                 17
% 3.31/1.01  unary:                                  18
% 3.31/1.01  binary:                                 4
% 3.31/1.01  lits:                                   98
% 3.31/1.01  lits_eq:                                8
% 3.31/1.01  fd_pure:                                0
% 3.31/1.01  fd_pseudo:                              0
% 3.31/1.01  fd_cond:                                0
% 3.31/1.01  fd_pseudo_cond:                         1
% 3.31/1.01  ac_symbols:                             0
% 3.31/1.01  
% 3.31/1.01  ------ Propositional Solver
% 3.31/1.01  
% 3.31/1.01  prop_solver_calls:                      28
% 3.31/1.01  prop_fast_solver_calls:                 1782
% 3.31/1.01  smt_solver_calls:                       0
% 3.31/1.01  smt_fast_solver_calls:                  0
% 3.31/1.01  prop_num_of_clauses:                    2218
% 3.31/1.01  prop_preprocess_simplified:             6712
% 3.31/1.01  prop_fo_subsumed:                       41
% 3.31/1.01  prop_solver_time:                       0.
% 3.31/1.01  smt_solver_time:                        0.
% 3.31/1.01  smt_fast_solver_time:                   0.
% 3.31/1.01  prop_fast_solver_time:                  0.
% 3.31/1.01  prop_unsat_core_time:                   0.
% 3.31/1.01  
% 3.31/1.01  ------ QBF
% 3.31/1.01  
% 3.31/1.01  qbf_q_res:                              0
% 3.31/1.01  qbf_num_tautologies:                    0
% 3.31/1.01  qbf_prep_cycles:                        0
% 3.31/1.01  
% 3.31/1.01  ------ BMC1
% 3.31/1.01  
% 3.31/1.01  bmc1_current_bound:                     -1
% 3.31/1.01  bmc1_last_solved_bound:                 -1
% 3.31/1.01  bmc1_unsat_core_size:                   -1
% 3.31/1.01  bmc1_unsat_core_parents_size:           -1
% 3.31/1.01  bmc1_merge_next_fun:                    0
% 3.31/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.31/1.01  
% 3.31/1.01  ------ Instantiation
% 3.31/1.01  
% 3.31/1.01  inst_num_of_clauses:                    601
% 3.31/1.01  inst_num_in_passive:                    13
% 3.31/1.01  inst_num_in_active:                     411
% 3.31/1.01  inst_num_in_unprocessed:                178
% 3.31/1.01  inst_num_of_loops:                      430
% 3.31/1.01  inst_num_of_learning_restarts:          0
% 3.31/1.01  inst_num_moves_active_passive:          15
% 3.31/1.01  inst_lit_activity:                      0
% 3.31/1.01  inst_lit_activity_moves:                0
% 3.31/1.01  inst_num_tautologies:                   0
% 3.31/1.01  inst_num_prop_implied:                  0
% 3.31/1.01  inst_num_existing_simplified:           0
% 3.31/1.01  inst_num_eq_res_simplified:             0
% 3.31/1.01  inst_num_child_elim:                    0
% 3.31/1.01  inst_num_of_dismatching_blockings:      131
% 3.31/1.01  inst_num_of_non_proper_insts:           1000
% 3.31/1.01  inst_num_of_duplicates:                 0
% 3.31/1.01  inst_inst_num_from_inst_to_res:         0
% 3.31/1.01  inst_dismatching_checking_time:         0.
% 3.31/1.01  
% 3.31/1.01  ------ Resolution
% 3.31/1.01  
% 3.31/1.01  res_num_of_clauses:                     0
% 3.31/1.01  res_num_in_passive:                     0
% 3.31/1.01  res_num_in_active:                      0
% 3.31/1.01  res_num_of_loops:                       180
% 3.31/1.01  res_forward_subset_subsumed:            131
% 3.31/1.01  res_backward_subset_subsumed:           6
% 3.31/1.01  res_forward_subsumed:                   0
% 3.31/1.01  res_backward_subsumed:                  0
% 3.31/1.01  res_forward_subsumption_resolution:     9
% 3.31/1.01  res_backward_subsumption_resolution:    0
% 3.31/1.01  res_clause_to_clause_subsumption:       631
% 3.31/1.01  res_orphan_elimination:                 0
% 3.31/1.01  res_tautology_del:                      126
% 3.31/1.01  res_num_eq_res_simplified:              0
% 3.31/1.01  res_num_sel_changes:                    0
% 3.31/1.01  res_moves_from_active_to_pass:          0
% 3.31/1.01  
% 3.31/1.01  ------ Superposition
% 3.31/1.01  
% 3.31/1.01  sup_time_total:                         0.
% 3.31/1.01  sup_time_generating:                    0.
% 3.31/1.01  sup_time_sim_full:                      0.
% 3.31/1.01  sup_time_sim_immed:                     0.
% 3.31/1.01  
% 3.31/1.01  sup_num_of_clauses:                     127
% 3.31/1.01  sup_num_in_active:                      69
% 3.31/1.01  sup_num_in_passive:                     58
% 3.31/1.01  sup_num_of_loops:                       84
% 3.31/1.01  sup_fw_superposition:                   76
% 3.31/1.01  sup_bw_superposition:                   49
% 3.31/1.01  sup_immediate_simplified:               26
% 3.31/1.01  sup_given_eliminated:                   0
% 3.31/1.01  comparisons_done:                       0
% 3.31/1.01  comparisons_avoided:                    0
% 3.31/1.01  
% 3.31/1.01  ------ Simplifications
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  sim_fw_subset_subsumed:                 12
% 3.31/1.01  sim_bw_subset_subsumed:                 2
% 3.31/1.01  sim_fw_subsumed:                        6
% 3.31/1.01  sim_bw_subsumed:                        0
% 3.31/1.01  sim_fw_subsumption_res:                 1
% 3.31/1.01  sim_bw_subsumption_res:                 0
% 3.31/1.01  sim_tautology_del:                      11
% 3.31/1.01  sim_eq_tautology_del:                   1
% 3.31/1.01  sim_eq_res_simp:                        0
% 3.31/1.01  sim_fw_demodulated:                     0
% 3.31/1.01  sim_bw_demodulated:                     16
% 3.31/1.01  sim_light_normalised:                   18
% 3.31/1.01  sim_joinable_taut:                      0
% 3.31/1.01  sim_joinable_simp:                      0
% 3.31/1.01  sim_ac_normalised:                      0
% 3.31/1.01  sim_smt_subsumption:                    0
% 3.31/1.01  
%------------------------------------------------------------------------------
