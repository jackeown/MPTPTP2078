%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:37 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  204 (1290 expanded)
%              Number of clauses        :  119 ( 328 expanded)
%              Number of leaves         :   23 ( 530 expanded)
%              Depth                    :   27
%              Number of atoms          : 1093 (16060 expanded)
%              Number of equality atoms :  334 (2517 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal clause size      :   38 (   5 average)
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f40])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f41,f50,f49,f48,f47,f46,f45,f44])).

fof(f87,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f58,plain,(
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

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f63,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f38])).

fof(f43,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f69])).

fof(f81,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f77,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f65,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
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

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2037,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2095,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2037,c_20])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2033,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2044,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3139,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2033,c_2044])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3513,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3139,c_39])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_399,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_2021,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_3518,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3513,c_2021])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_516,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_517,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_521,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_hidden(X4,X5)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(X5,X3)
    | ~ r1_tarski(X5,u1_struct_0(X0))
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
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_26])).

cnf(c_522,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(renaming,[status(thm)],[c_521])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_571,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_522,c_3,c_15])).

cnf(c_595,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | k2_struct_0(X6) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_571])).

cnf(c_596,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_642,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_596,c_4,c_7])).

cnf(c_2020,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
    | r1_tarski(k2_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_2823,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2020])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5498,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2823,c_40,c_41,c_42])).

cnf(c_5499,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5498])).

cnf(c_2029,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2941,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2029,c_2021])).

cnf(c_5502,plain,
    ( u1_struct_0(X0) != k2_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5499,c_2941,c_3518])).

cnf(c_5522,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_5502])).

cnf(c_5601,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5522,c_3518])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2034,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3323,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2941,c_2034])).

cnf(c_4144,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3518,c_3323])).

cnf(c_17542,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5601,c_45,c_4144])).

cnf(c_17543,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17542])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2048,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2080,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2048,c_0])).

cnf(c_17560,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17543,c_2080])).

cnf(c_17564,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2095,c_17560])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2031,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3140,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_2044])).

cnf(c_3520,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3140,c_39])).

cnf(c_3525,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3520,c_2021])).

cnf(c_17576,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17564,c_3525])).

cnf(c_14,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2040,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4156,plain,
    ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_2040])).

cnf(c_6412,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3525,c_4156])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2041,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2043,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4685,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3525,c_2043])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4359,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3525,c_23])).

cnf(c_4717,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4685,c_4359])).

cnf(c_5101,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4717,c_39,c_3140])).

cnf(c_5102,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5101])).

cnf(c_5110,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2041,c_5102])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_191,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_7])).

cnf(c_192,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_2023,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_4624,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3525,c_2023])).

cnf(c_4661,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4624,c_4359])).

cnf(c_4995,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4661,c_39,c_3140])).

cnf(c_4996,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4995])).

cnf(c_5003,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2041,c_4996])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2036,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2075,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2036,c_20])).

cnf(c_4358,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3525,c_2075])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2035,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2047,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3155,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2035,c_2047])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2338,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2339,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_385,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_6,c_8])).

cnf(c_2429,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_2430,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_3584,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3155,c_39,c_45,c_50,c_2339,c_2430,c_3139])).

cnf(c_4143,plain,
    ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3518,c_3584])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_53,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17576,c_6412,c_5110,c_5003,c_4358,c_4143,c_3140,c_3139,c_53,c_46,c_43,c_39,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.87/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.00  
% 3.87/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/1.00  
% 3.87/1.00  ------  iProver source info
% 3.87/1.00  
% 3.87/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.87/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/1.00  git: non_committed_changes: false
% 3.87/1.00  git: last_make_outside_of_git: false
% 3.87/1.00  
% 3.87/1.00  ------ 
% 3.87/1.00  
% 3.87/1.00  ------ Input Options
% 3.87/1.00  
% 3.87/1.00  --out_options                           all
% 3.87/1.00  --tptp_safe_out                         true
% 3.87/1.00  --problem_path                          ""
% 3.87/1.00  --include_path                          ""
% 3.87/1.00  --clausifier                            res/vclausify_rel
% 3.87/1.00  --clausifier_options                    --mode clausify
% 3.87/1.00  --stdin                                 false
% 3.87/1.00  --stats_out                             all
% 3.87/1.00  
% 3.87/1.00  ------ General Options
% 3.87/1.00  
% 3.87/1.00  --fof                                   false
% 3.87/1.00  --time_out_real                         305.
% 3.87/1.00  --time_out_virtual                      -1.
% 3.87/1.00  --symbol_type_check                     false
% 3.87/1.00  --clausify_out                          false
% 3.87/1.00  --sig_cnt_out                           false
% 3.87/1.00  --trig_cnt_out                          false
% 3.87/1.00  --trig_cnt_out_tolerance                1.
% 3.87/1.00  --trig_cnt_out_sk_spl                   false
% 3.87/1.00  --abstr_cl_out                          false
% 3.87/1.00  
% 3.87/1.00  ------ Global Options
% 3.87/1.00  
% 3.87/1.00  --schedule                              default
% 3.87/1.00  --add_important_lit                     false
% 3.87/1.00  --prop_solver_per_cl                    1000
% 3.87/1.00  --min_unsat_core                        false
% 3.87/1.00  --soft_assumptions                      false
% 3.87/1.00  --soft_lemma_size                       3
% 3.87/1.00  --prop_impl_unit_size                   0
% 3.87/1.00  --prop_impl_unit                        []
% 3.87/1.00  --share_sel_clauses                     true
% 3.87/1.00  --reset_solvers                         false
% 3.87/1.00  --bc_imp_inh                            [conj_cone]
% 3.87/1.00  --conj_cone_tolerance                   3.
% 3.87/1.00  --extra_neg_conj                        none
% 3.87/1.00  --large_theory_mode                     true
% 3.87/1.00  --prolific_symb_bound                   200
% 3.87/1.00  --lt_threshold                          2000
% 3.87/1.00  --clause_weak_htbl                      true
% 3.87/1.00  --gc_record_bc_elim                     false
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing Options
% 3.87/1.00  
% 3.87/1.00  --preprocessing_flag                    true
% 3.87/1.00  --time_out_prep_mult                    0.1
% 3.87/1.00  --splitting_mode                        input
% 3.87/1.00  --splitting_grd                         true
% 3.87/1.00  --splitting_cvd                         false
% 3.87/1.00  --splitting_cvd_svl                     false
% 3.87/1.00  --splitting_nvd                         32
% 3.87/1.00  --sub_typing                            true
% 3.87/1.00  --prep_gs_sim                           true
% 3.87/1.00  --prep_unflatten                        true
% 3.87/1.00  --prep_res_sim                          true
% 3.87/1.00  --prep_upred                            true
% 3.87/1.00  --prep_sem_filter                       exhaustive
% 3.87/1.00  --prep_sem_filter_out                   false
% 3.87/1.00  --pred_elim                             true
% 3.87/1.00  --res_sim_input                         true
% 3.87/1.00  --eq_ax_congr_red                       true
% 3.87/1.00  --pure_diseq_elim                       true
% 3.87/1.00  --brand_transform                       false
% 3.87/1.00  --non_eq_to_eq                          false
% 3.87/1.00  --prep_def_merge                        true
% 3.87/1.00  --prep_def_merge_prop_impl              false
% 3.87/1.00  --prep_def_merge_mbd                    true
% 3.87/1.00  --prep_def_merge_tr_red                 false
% 3.87/1.00  --prep_def_merge_tr_cl                  false
% 3.87/1.00  --smt_preprocessing                     true
% 3.87/1.00  --smt_ac_axioms                         fast
% 3.87/1.00  --preprocessed_out                      false
% 3.87/1.00  --preprocessed_stats                    false
% 3.87/1.00  
% 3.87/1.00  ------ Abstraction refinement Options
% 3.87/1.00  
% 3.87/1.00  --abstr_ref                             []
% 3.87/1.00  --abstr_ref_prep                        false
% 3.87/1.00  --abstr_ref_until_sat                   false
% 3.87/1.00  --abstr_ref_sig_restrict                funpre
% 3.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/1.00  --abstr_ref_under                       []
% 3.87/1.00  
% 3.87/1.00  ------ SAT Options
% 3.87/1.00  
% 3.87/1.00  --sat_mode                              false
% 3.87/1.00  --sat_fm_restart_options                ""
% 3.87/1.00  --sat_gr_def                            false
% 3.87/1.00  --sat_epr_types                         true
% 3.87/1.00  --sat_non_cyclic_types                  false
% 3.87/1.00  --sat_finite_models                     false
% 3.87/1.00  --sat_fm_lemmas                         false
% 3.87/1.00  --sat_fm_prep                           false
% 3.87/1.00  --sat_fm_uc_incr                        true
% 3.87/1.00  --sat_out_model                         small
% 3.87/1.00  --sat_out_clauses                       false
% 3.87/1.00  
% 3.87/1.00  ------ QBF Options
% 3.87/1.00  
% 3.87/1.00  --qbf_mode                              false
% 3.87/1.00  --qbf_elim_univ                         false
% 3.87/1.00  --qbf_dom_inst                          none
% 3.87/1.00  --qbf_dom_pre_inst                      false
% 3.87/1.00  --qbf_sk_in                             false
% 3.87/1.00  --qbf_pred_elim                         true
% 3.87/1.00  --qbf_split                             512
% 3.87/1.00  
% 3.87/1.00  ------ BMC1 Options
% 3.87/1.00  
% 3.87/1.00  --bmc1_incremental                      false
% 3.87/1.00  --bmc1_axioms                           reachable_all
% 3.87/1.00  --bmc1_min_bound                        0
% 3.87/1.00  --bmc1_max_bound                        -1
% 3.87/1.00  --bmc1_max_bound_default                -1
% 3.87/1.00  --bmc1_symbol_reachability              true
% 3.87/1.00  --bmc1_property_lemmas                  false
% 3.87/1.00  --bmc1_k_induction                      false
% 3.87/1.00  --bmc1_non_equiv_states                 false
% 3.87/1.00  --bmc1_deadlock                         false
% 3.87/1.00  --bmc1_ucm                              false
% 3.87/1.00  --bmc1_add_unsat_core                   none
% 3.87/1.00  --bmc1_unsat_core_children              false
% 3.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/1.00  --bmc1_out_stat                         full
% 3.87/1.00  --bmc1_ground_init                      false
% 3.87/1.00  --bmc1_pre_inst_next_state              false
% 3.87/1.00  --bmc1_pre_inst_state                   false
% 3.87/1.00  --bmc1_pre_inst_reach_state             false
% 3.87/1.00  --bmc1_out_unsat_core                   false
% 3.87/1.00  --bmc1_aig_witness_out                  false
% 3.87/1.00  --bmc1_verbose                          false
% 3.87/1.00  --bmc1_dump_clauses_tptp                false
% 3.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.87/1.00  --bmc1_dump_file                        -
% 3.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.87/1.00  --bmc1_ucm_extend_mode                  1
% 3.87/1.00  --bmc1_ucm_init_mode                    2
% 3.87/1.00  --bmc1_ucm_cone_mode                    none
% 3.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.87/1.00  --bmc1_ucm_relax_model                  4
% 3.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/1.00  --bmc1_ucm_layered_model                none
% 3.87/1.00  --bmc1_ucm_max_lemma_size               10
% 3.87/1.00  
% 3.87/1.00  ------ AIG Options
% 3.87/1.00  
% 3.87/1.00  --aig_mode                              false
% 3.87/1.00  
% 3.87/1.00  ------ Instantiation Options
% 3.87/1.00  
% 3.87/1.00  --instantiation_flag                    true
% 3.87/1.00  --inst_sos_flag                         false
% 3.87/1.00  --inst_sos_phase                        true
% 3.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel_side                     num_symb
% 3.87/1.00  --inst_solver_per_active                1400
% 3.87/1.00  --inst_solver_calls_frac                1.
% 3.87/1.00  --inst_passive_queue_type               priority_queues
% 3.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/1.00  --inst_passive_queues_freq              [25;2]
% 3.87/1.00  --inst_dismatching                      true
% 3.87/1.00  --inst_eager_unprocessed_to_passive     true
% 3.87/1.00  --inst_prop_sim_given                   true
% 3.87/1.00  --inst_prop_sim_new                     false
% 3.87/1.00  --inst_subs_new                         false
% 3.87/1.00  --inst_eq_res_simp                      false
% 3.87/1.00  --inst_subs_given                       false
% 3.87/1.00  --inst_orphan_elimination               true
% 3.87/1.00  --inst_learning_loop_flag               true
% 3.87/1.00  --inst_learning_start                   3000
% 3.87/1.00  --inst_learning_factor                  2
% 3.87/1.00  --inst_start_prop_sim_after_learn       3
% 3.87/1.00  --inst_sel_renew                        solver
% 3.87/1.00  --inst_lit_activity_flag                true
% 3.87/1.00  --inst_restr_to_given                   false
% 3.87/1.00  --inst_activity_threshold               500
% 3.87/1.00  --inst_out_proof                        true
% 3.87/1.00  
% 3.87/1.00  ------ Resolution Options
% 3.87/1.00  
% 3.87/1.00  --resolution_flag                       true
% 3.87/1.00  --res_lit_sel                           adaptive
% 3.87/1.00  --res_lit_sel_side                      none
% 3.87/1.00  --res_ordering                          kbo
% 3.87/1.00  --res_to_prop_solver                    active
% 3.87/1.00  --res_prop_simpl_new                    false
% 3.87/1.00  --res_prop_simpl_given                  true
% 3.87/1.00  --res_passive_queue_type                priority_queues
% 3.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/1.00  --res_passive_queues_freq               [15;5]
% 3.87/1.00  --res_forward_subs                      full
% 3.87/1.00  --res_backward_subs                     full
% 3.87/1.00  --res_forward_subs_resolution           true
% 3.87/1.00  --res_backward_subs_resolution          true
% 3.87/1.00  --res_orphan_elimination                true
% 3.87/1.00  --res_time_limit                        2.
% 3.87/1.00  --res_out_proof                         true
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Options
% 3.87/1.00  
% 3.87/1.00  --superposition_flag                    true
% 3.87/1.00  --sup_passive_queue_type                priority_queues
% 3.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.87/1.00  --demod_completeness_check              fast
% 3.87/1.00  --demod_use_ground                      true
% 3.87/1.00  --sup_to_prop_solver                    passive
% 3.87/1.00  --sup_prop_simpl_new                    true
% 3.87/1.00  --sup_prop_simpl_given                  true
% 3.87/1.00  --sup_fun_splitting                     false
% 3.87/1.00  --sup_smt_interval                      50000
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Simplification Setup
% 3.87/1.00  
% 3.87/1.00  --sup_indices_passive                   []
% 3.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_full_bw                           [BwDemod]
% 3.87/1.00  --sup_immed_triv                        [TrivRules]
% 3.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_immed_bw_main                     []
% 3.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  
% 3.87/1.00  ------ Combination Options
% 3.87/1.00  
% 3.87/1.00  --comb_res_mult                         3
% 3.87/1.00  --comb_sup_mult                         2
% 3.87/1.00  --comb_inst_mult                        10
% 3.87/1.00  
% 3.87/1.00  ------ Debug Options
% 3.87/1.00  
% 3.87/1.00  --dbg_backtrace                         false
% 3.87/1.00  --dbg_dump_prop_clauses                 false
% 3.87/1.00  --dbg_dump_prop_clauses_file            -
% 3.87/1.00  --dbg_out_stat                          false
% 3.87/1.00  ------ Parsing...
% 3.87/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/1.00  ------ Proving...
% 3.87/1.00  ------ Problem Properties 
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  clauses                                 33
% 3.87/1.00  conjectures                             17
% 3.87/1.00  EPR                                     17
% 3.87/1.00  Horn                                    30
% 3.87/1.00  unary                                   19
% 3.87/1.00  binary                                  2
% 3.87/1.00  lits                                    95
% 3.87/1.00  lits eq                                 8
% 3.87/1.00  fd_pure                                 0
% 3.87/1.00  fd_pseudo                               0
% 3.87/1.00  fd_cond                                 0
% 3.87/1.00  fd_pseudo_cond                          0
% 3.87/1.00  AC symbols                              0
% 3.87/1.00  
% 3.87/1.00  ------ Schedule dynamic 5 is on 
% 3.87/1.00  
% 3.87/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  ------ 
% 3.87/1.00  Current options:
% 3.87/1.00  ------ 
% 3.87/1.00  
% 3.87/1.00  ------ Input Options
% 3.87/1.00  
% 3.87/1.00  --out_options                           all
% 3.87/1.00  --tptp_safe_out                         true
% 3.87/1.00  --problem_path                          ""
% 3.87/1.00  --include_path                          ""
% 3.87/1.00  --clausifier                            res/vclausify_rel
% 3.87/1.00  --clausifier_options                    --mode clausify
% 3.87/1.00  --stdin                                 false
% 3.87/1.00  --stats_out                             all
% 3.87/1.00  
% 3.87/1.00  ------ General Options
% 3.87/1.00  
% 3.87/1.00  --fof                                   false
% 3.87/1.00  --time_out_real                         305.
% 3.87/1.00  --time_out_virtual                      -1.
% 3.87/1.00  --symbol_type_check                     false
% 3.87/1.00  --clausify_out                          false
% 3.87/1.00  --sig_cnt_out                           false
% 3.87/1.00  --trig_cnt_out                          false
% 3.87/1.00  --trig_cnt_out_tolerance                1.
% 3.87/1.00  --trig_cnt_out_sk_spl                   false
% 3.87/1.00  --abstr_cl_out                          false
% 3.87/1.00  
% 3.87/1.00  ------ Global Options
% 3.87/1.00  
% 3.87/1.00  --schedule                              default
% 3.87/1.00  --add_important_lit                     false
% 3.87/1.00  --prop_solver_per_cl                    1000
% 3.87/1.00  --min_unsat_core                        false
% 3.87/1.00  --soft_assumptions                      false
% 3.87/1.00  --soft_lemma_size                       3
% 3.87/1.00  --prop_impl_unit_size                   0
% 3.87/1.00  --prop_impl_unit                        []
% 3.87/1.00  --share_sel_clauses                     true
% 3.87/1.00  --reset_solvers                         false
% 3.87/1.00  --bc_imp_inh                            [conj_cone]
% 3.87/1.00  --conj_cone_tolerance                   3.
% 3.87/1.00  --extra_neg_conj                        none
% 3.87/1.00  --large_theory_mode                     true
% 3.87/1.00  --prolific_symb_bound                   200
% 3.87/1.00  --lt_threshold                          2000
% 3.87/1.00  --clause_weak_htbl                      true
% 3.87/1.00  --gc_record_bc_elim                     false
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing Options
% 3.87/1.00  
% 3.87/1.00  --preprocessing_flag                    true
% 3.87/1.00  --time_out_prep_mult                    0.1
% 3.87/1.00  --splitting_mode                        input
% 3.87/1.00  --splitting_grd                         true
% 3.87/1.00  --splitting_cvd                         false
% 3.87/1.00  --splitting_cvd_svl                     false
% 3.87/1.00  --splitting_nvd                         32
% 3.87/1.00  --sub_typing                            true
% 3.87/1.00  --prep_gs_sim                           true
% 3.87/1.00  --prep_unflatten                        true
% 3.87/1.00  --prep_res_sim                          true
% 3.87/1.00  --prep_upred                            true
% 3.87/1.00  --prep_sem_filter                       exhaustive
% 3.87/1.00  --prep_sem_filter_out                   false
% 3.87/1.00  --pred_elim                             true
% 3.87/1.00  --res_sim_input                         true
% 3.87/1.00  --eq_ax_congr_red                       true
% 3.87/1.00  --pure_diseq_elim                       true
% 3.87/1.00  --brand_transform                       false
% 3.87/1.00  --non_eq_to_eq                          false
% 3.87/1.00  --prep_def_merge                        true
% 3.87/1.00  --prep_def_merge_prop_impl              false
% 3.87/1.00  --prep_def_merge_mbd                    true
% 3.87/1.00  --prep_def_merge_tr_red                 false
% 3.87/1.00  --prep_def_merge_tr_cl                  false
% 3.87/1.00  --smt_preprocessing                     true
% 3.87/1.00  --smt_ac_axioms                         fast
% 3.87/1.00  --preprocessed_out                      false
% 3.87/1.00  --preprocessed_stats                    false
% 3.87/1.00  
% 3.87/1.00  ------ Abstraction refinement Options
% 3.87/1.00  
% 3.87/1.00  --abstr_ref                             []
% 3.87/1.00  --abstr_ref_prep                        false
% 3.87/1.00  --abstr_ref_until_sat                   false
% 3.87/1.00  --abstr_ref_sig_restrict                funpre
% 3.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/1.00  --abstr_ref_under                       []
% 3.87/1.00  
% 3.87/1.00  ------ SAT Options
% 3.87/1.00  
% 3.87/1.00  --sat_mode                              false
% 3.87/1.00  --sat_fm_restart_options                ""
% 3.87/1.00  --sat_gr_def                            false
% 3.87/1.00  --sat_epr_types                         true
% 3.87/1.00  --sat_non_cyclic_types                  false
% 3.87/1.00  --sat_finite_models                     false
% 3.87/1.00  --sat_fm_lemmas                         false
% 3.87/1.00  --sat_fm_prep                           false
% 3.87/1.00  --sat_fm_uc_incr                        true
% 3.87/1.00  --sat_out_model                         small
% 3.87/1.00  --sat_out_clauses                       false
% 3.87/1.00  
% 3.87/1.00  ------ QBF Options
% 3.87/1.00  
% 3.87/1.00  --qbf_mode                              false
% 3.87/1.00  --qbf_elim_univ                         false
% 3.87/1.00  --qbf_dom_inst                          none
% 3.87/1.00  --qbf_dom_pre_inst                      false
% 3.87/1.00  --qbf_sk_in                             false
% 3.87/1.00  --qbf_pred_elim                         true
% 3.87/1.00  --qbf_split                             512
% 3.87/1.00  
% 3.87/1.00  ------ BMC1 Options
% 3.87/1.00  
% 3.87/1.00  --bmc1_incremental                      false
% 3.87/1.00  --bmc1_axioms                           reachable_all
% 3.87/1.00  --bmc1_min_bound                        0
% 3.87/1.00  --bmc1_max_bound                        -1
% 3.87/1.00  --bmc1_max_bound_default                -1
% 3.87/1.00  --bmc1_symbol_reachability              true
% 3.87/1.00  --bmc1_property_lemmas                  false
% 3.87/1.00  --bmc1_k_induction                      false
% 3.87/1.00  --bmc1_non_equiv_states                 false
% 3.87/1.00  --bmc1_deadlock                         false
% 3.87/1.00  --bmc1_ucm                              false
% 3.87/1.00  --bmc1_add_unsat_core                   none
% 3.87/1.00  --bmc1_unsat_core_children              false
% 3.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/1.00  --bmc1_out_stat                         full
% 3.87/1.00  --bmc1_ground_init                      false
% 3.87/1.00  --bmc1_pre_inst_next_state              false
% 3.87/1.00  --bmc1_pre_inst_state                   false
% 3.87/1.00  --bmc1_pre_inst_reach_state             false
% 3.87/1.00  --bmc1_out_unsat_core                   false
% 3.87/1.00  --bmc1_aig_witness_out                  false
% 3.87/1.00  --bmc1_verbose                          false
% 3.87/1.00  --bmc1_dump_clauses_tptp                false
% 3.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.87/1.00  --bmc1_dump_file                        -
% 3.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.87/1.00  --bmc1_ucm_extend_mode                  1
% 3.87/1.00  --bmc1_ucm_init_mode                    2
% 3.87/1.00  --bmc1_ucm_cone_mode                    none
% 3.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.87/1.00  --bmc1_ucm_relax_model                  4
% 3.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/1.00  --bmc1_ucm_layered_model                none
% 3.87/1.00  --bmc1_ucm_max_lemma_size               10
% 3.87/1.00  
% 3.87/1.00  ------ AIG Options
% 3.87/1.00  
% 3.87/1.00  --aig_mode                              false
% 3.87/1.00  
% 3.87/1.00  ------ Instantiation Options
% 3.87/1.00  
% 3.87/1.00  --instantiation_flag                    true
% 3.87/1.00  --inst_sos_flag                         false
% 3.87/1.00  --inst_sos_phase                        true
% 3.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel_side                     none
% 3.87/1.00  --inst_solver_per_active                1400
% 3.87/1.00  --inst_solver_calls_frac                1.
% 3.87/1.00  --inst_passive_queue_type               priority_queues
% 3.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/1.00  --inst_passive_queues_freq              [25;2]
% 3.87/1.00  --inst_dismatching                      true
% 3.87/1.00  --inst_eager_unprocessed_to_passive     true
% 3.87/1.00  --inst_prop_sim_given                   true
% 3.87/1.00  --inst_prop_sim_new                     false
% 3.87/1.00  --inst_subs_new                         false
% 3.87/1.00  --inst_eq_res_simp                      false
% 3.87/1.00  --inst_subs_given                       false
% 3.87/1.00  --inst_orphan_elimination               true
% 3.87/1.00  --inst_learning_loop_flag               true
% 3.87/1.00  --inst_learning_start                   3000
% 3.87/1.00  --inst_learning_factor                  2
% 3.87/1.00  --inst_start_prop_sim_after_learn       3
% 3.87/1.00  --inst_sel_renew                        solver
% 3.87/1.00  --inst_lit_activity_flag                true
% 3.87/1.00  --inst_restr_to_given                   false
% 3.87/1.00  --inst_activity_threshold               500
% 3.87/1.00  --inst_out_proof                        true
% 3.87/1.00  
% 3.87/1.00  ------ Resolution Options
% 3.87/1.00  
% 3.87/1.00  --resolution_flag                       false
% 3.87/1.00  --res_lit_sel                           adaptive
% 3.87/1.00  --res_lit_sel_side                      none
% 3.87/1.00  --res_ordering                          kbo
% 3.87/1.00  --res_to_prop_solver                    active
% 3.87/1.00  --res_prop_simpl_new                    false
% 3.87/1.00  --res_prop_simpl_given                  true
% 3.87/1.00  --res_passive_queue_type                priority_queues
% 3.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/1.00  --res_passive_queues_freq               [15;5]
% 3.87/1.00  --res_forward_subs                      full
% 3.87/1.00  --res_backward_subs                     full
% 3.87/1.00  --res_forward_subs_resolution           true
% 3.87/1.00  --res_backward_subs_resolution          true
% 3.87/1.00  --res_orphan_elimination                true
% 3.87/1.00  --res_time_limit                        2.
% 3.87/1.00  --res_out_proof                         true
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Options
% 3.87/1.00  
% 3.87/1.00  --superposition_flag                    true
% 3.87/1.00  --sup_passive_queue_type                priority_queues
% 3.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.87/1.00  --demod_completeness_check              fast
% 3.87/1.00  --demod_use_ground                      true
% 3.87/1.00  --sup_to_prop_solver                    passive
% 3.87/1.00  --sup_prop_simpl_new                    true
% 3.87/1.00  --sup_prop_simpl_given                  true
% 3.87/1.00  --sup_fun_splitting                     false
% 3.87/1.00  --sup_smt_interval                      50000
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Simplification Setup
% 3.87/1.00  
% 3.87/1.00  --sup_indices_passive                   []
% 3.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_full_bw                           [BwDemod]
% 3.87/1.00  --sup_immed_triv                        [TrivRules]
% 3.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_immed_bw_main                     []
% 3.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  
% 3.87/1.00  ------ Combination Options
% 3.87/1.00  
% 3.87/1.00  --comb_res_mult                         3
% 3.87/1.00  --comb_sup_mult                         2
% 3.87/1.00  --comb_inst_mult                        10
% 3.87/1.00  
% 3.87/1.00  ------ Debug Options
% 3.87/1.00  
% 3.87/1.00  --dbg_backtrace                         false
% 3.87/1.00  --dbg_dump_prop_clauses                 false
% 3.87/1.00  --dbg_dump_prop_clauses_file            -
% 3.87/1.00  --dbg_out_stat                          false
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  ------ Proving...
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  % SZS status Theorem for theBenchmark.p
% 3.87/1.00  
% 3.87/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/1.00  
% 3.87/1.00  fof(f17,conjecture,(
% 3.87/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f18,negated_conjecture,(
% 3.87/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.87/1.00    inference(negated_conjecture,[],[f17])).
% 3.87/1.00  
% 3.87/1.00  fof(f40,plain,(
% 3.87/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f18])).
% 3.87/1.00  
% 3.87/1.00  fof(f41,plain,(
% 3.87/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.87/1.00    inference(flattening,[],[f40])).
% 3.87/1.00  
% 3.87/1.00  fof(f50,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f49,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f48,plain,(
% 3.87/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f47,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f46,plain,(
% 3.87/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f45,plain,(
% 3.87/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f44,plain,(
% 3.87/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f51,plain,(
% 3.87/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.87/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f41,f50,f49,f48,f47,f46,f45,f44])).
% 3.87/1.00  
% 3.87/1.00  fof(f87,plain,(
% 3.87/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f86,plain,(
% 3.87/1.00    sK5 = sK6),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f79,plain,(
% 3.87/1.00    m1_pre_topc(sK3,sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f8,axiom,(
% 3.87/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f27,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f8])).
% 3.87/1.00  
% 3.87/1.00  fof(f59,plain,(
% 3.87/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f27])).
% 3.87/1.00  
% 3.87/1.00  fof(f72,plain,(
% 3.87/1.00    l1_pre_topc(sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f7,axiom,(
% 3.87/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f26,plain,(
% 3.87/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f7])).
% 3.87/1.00  
% 3.87/1.00  fof(f58,plain,(
% 3.87/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f26])).
% 3.87/1.00  
% 3.87/1.00  fof(f6,axiom,(
% 3.87/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f25,plain,(
% 3.87/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f6])).
% 3.87/1.00  
% 3.87/1.00  fof(f57,plain,(
% 3.87/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f25])).
% 3.87/1.00  
% 3.87/1.00  fof(f11,axiom,(
% 3.87/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f31,plain,(
% 3.87/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f11])).
% 3.87/1.00  
% 3.87/1.00  fof(f32,plain,(
% 3.87/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.87/1.00    inference(flattening,[],[f31])).
% 3.87/1.00  
% 3.87/1.00  fof(f63,plain,(
% 3.87/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f32])).
% 3.87/1.00  
% 3.87/1.00  fof(f16,axiom,(
% 3.87/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f38,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f16])).
% 3.87/1.00  
% 3.87/1.00  fof(f39,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.87/1.00    inference(flattening,[],[f38])).
% 3.87/1.00  
% 3.87/1.00  fof(f43,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.87/1.00    inference(nnf_transformation,[],[f39])).
% 3.87/1.00  
% 3.87/1.00  fof(f69,plain,(
% 3.87/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f43])).
% 3.87/1.00  
% 3.87/1.00  fof(f89,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/1.00    inference(equality_resolution,[],[f69])).
% 3.87/1.00  
% 3.87/1.00  fof(f81,plain,(
% 3.87/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f80,plain,(
% 3.87/1.00    v1_funct_1(sK4)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f4,axiom,(
% 3.87/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f21,plain,(
% 3.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.87/1.00    inference(ennf_transformation,[],[f4])).
% 3.87/1.00  
% 3.87/1.00  fof(f22,plain,(
% 3.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.87/1.00    inference(flattening,[],[f21])).
% 3.87/1.00  
% 3.87/1.00  fof(f55,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f22])).
% 3.87/1.00  
% 3.87/1.00  fof(f15,axiom,(
% 3.87/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f36,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f15])).
% 3.87/1.00  
% 3.87/1.00  fof(f37,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.87/1.00    inference(flattening,[],[f36])).
% 3.87/1.00  
% 3.87/1.00  fof(f67,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f37])).
% 3.87/1.00  
% 3.87/1.00  fof(f5,axiom,(
% 3.87/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f23,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f5])).
% 3.87/1.00  
% 3.87/1.00  fof(f24,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.87/1.00    inference(flattening,[],[f23])).
% 3.87/1.00  
% 3.87/1.00  fof(f56,plain,(
% 3.87/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f24])).
% 3.87/1.00  
% 3.87/1.00  fof(f73,plain,(
% 3.87/1.00    ~v2_struct_0(sK1)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f74,plain,(
% 3.87/1.00    v2_pre_topc(sK1)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f75,plain,(
% 3.87/1.00    l1_pre_topc(sK1)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f78,plain,(
% 3.87/1.00    ~v2_struct_0(sK3)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f82,plain,(
% 3.87/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f2,axiom,(
% 3.87/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f53,plain,(
% 3.87/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.87/1.00    inference(cnf_transformation,[],[f2])).
% 3.87/1.00  
% 3.87/1.00  fof(f1,axiom,(
% 3.87/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f52,plain,(
% 3.87/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.87/1.00    inference(cnf_transformation,[],[f1])).
% 3.87/1.00  
% 3.87/1.00  fof(f77,plain,(
% 3.87/1.00    m1_pre_topc(sK2,sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f14,axiom,(
% 3.87/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f35,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f14])).
% 3.87/1.00  
% 3.87/1.00  fof(f66,plain,(
% 3.87/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f35])).
% 3.87/1.00  
% 3.87/1.00  fof(f13,axiom,(
% 3.87/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f34,plain,(
% 3.87/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f13])).
% 3.87/1.00  
% 3.87/1.00  fof(f65,plain,(
% 3.87/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f34])).
% 3.87/1.00  
% 3.87/1.00  fof(f10,axiom,(
% 3.87/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f30,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f10])).
% 3.87/1.00  
% 3.87/1.00  fof(f42,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.87/1.00    inference(nnf_transformation,[],[f30])).
% 3.87/1.00  
% 3.87/1.00  fof(f62,plain,(
% 3.87/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f42])).
% 3.87/1.00  
% 3.87/1.00  fof(f83,plain,(
% 3.87/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f61,plain,(
% 3.87/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f42])).
% 3.87/1.00  
% 3.87/1.00  fof(f85,plain,(
% 3.87/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f84,plain,(
% 3.87/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f3,axiom,(
% 3.87/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f19,plain,(
% 3.87/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.87/1.00    inference(ennf_transformation,[],[f3])).
% 3.87/1.00  
% 3.87/1.00  fof(f20,plain,(
% 3.87/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.87/1.00    inference(flattening,[],[f19])).
% 3.87/1.00  
% 3.87/1.00  fof(f54,plain,(
% 3.87/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f20])).
% 3.87/1.00  
% 3.87/1.00  fof(f9,axiom,(
% 3.87/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f28,plain,(
% 3.87/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f9])).
% 3.87/1.00  
% 3.87/1.00  fof(f29,plain,(
% 3.87/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.87/1.00    inference(flattening,[],[f28])).
% 3.87/1.00  
% 3.87/1.00  fof(f60,plain,(
% 3.87/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f29])).
% 3.87/1.00  
% 3.87/1.00  fof(f88,plain,(
% 3.87/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f76,plain,(
% 3.87/1.00    ~v2_struct_0(sK2)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f71,plain,(
% 3.87/1.00    v2_pre_topc(sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  fof(f70,plain,(
% 3.87/1.00    ~v2_struct_0(sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f51])).
% 3.87/1.00  
% 3.87/1.00  cnf(c_19,negated_conjecture,
% 3.87/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.87/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2037,plain,
% 3.87/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_20,negated_conjecture,
% 3.87/1.00      ( sK5 = sK6 ),
% 3.87/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2095,plain,
% 3.87/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.87/1.00      inference(light_normalisation,[status(thm)],[c_2037,c_20]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_27,negated_conjecture,
% 3.87/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2033,plain,
% 3.87/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_7,plain,
% 3.87/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2044,plain,
% 3.87/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.87/1.00      | l1_pre_topc(X1) != iProver_top
% 3.87/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3139,plain,
% 3.87/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.87/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_2033,c_2044]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_34,negated_conjecture,
% 3.87/1.00      ( l1_pre_topc(sK0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_39,plain,
% 3.87/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3513,plain,
% 3.87/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_3139,c_39]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_6,plain,
% 3.87/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_5,plain,
% 3.87/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_399,plain,
% 3.87/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.87/1.00      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2021,plain,
% 3.87/1.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.87/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3518,plain,
% 3.87/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_3513,c_2021]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_11,plain,
% 3.87/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.87/1.00      | ~ l1_pre_topc(X0)
% 3.87/1.00      | ~ v2_pre_topc(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_16,plain,
% 3.87/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.87/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.87/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.87/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.87/1.00      | ~ v3_pre_topc(X6,X0)
% 3.87/1.00      | ~ m1_pre_topc(X4,X5)
% 3.87/1.00      | ~ m1_pre_topc(X4,X0)
% 3.87/1.00      | ~ m1_pre_topc(X0,X5)
% 3.87/1.00      | ~ r2_hidden(X3,X6)
% 3.87/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.87/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.87/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.87/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.87/1.00      | ~ v1_funct_1(X2)
% 3.87/1.00      | v2_struct_0(X5)
% 3.87/1.00      | v2_struct_0(X1)
% 3.87/1.00      | v2_struct_0(X4)
% 3.87/1.00      | v2_struct_0(X0)
% 3.87/1.00      | ~ l1_pre_topc(X5)
% 3.87/1.00      | ~ l1_pre_topc(X1)
% 3.87/1.00      | ~ v2_pre_topc(X5)
% 3.87/1.00      | ~ v2_pre_topc(X1) ),
% 3.87/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_25,negated_conjecture,
% 3.87/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.87/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_516,plain,
% 3.87/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.87/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.87/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.87/1.00      | ~ v3_pre_topc(X6,X0)
% 3.87/1.00      | ~ m1_pre_topc(X4,X5)
% 3.87/1.00      | ~ m1_pre_topc(X4,X0)
% 3.87/1.00      | ~ m1_pre_topc(X0,X5)
% 3.87/1.00      | ~ r2_hidden(X3,X6)
% 3.87/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.87/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.87/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.87/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.87/1.00      | ~ v1_funct_1(X2)
% 3.87/1.00      | v2_struct_0(X0)
% 3.87/1.00      | v2_struct_0(X1)
% 3.87/1.00      | v2_struct_0(X5)
% 3.87/1.00      | v2_struct_0(X4)
% 3.87/1.00      | ~ l1_pre_topc(X1)
% 3.87/1.00      | ~ l1_pre_topc(X5)
% 3.87/1.00      | ~ v2_pre_topc(X1)
% 3.87/1.00      | ~ v2_pre_topc(X5)
% 3.87/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/1.00      | sK4 != X2 ),
% 3.87/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_517,plain,
% 3.87/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.87/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.87/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.87/1.00      | ~ v3_pre_topc(X5,X3)
% 3.87/1.00      | ~ m1_pre_topc(X0,X2)
% 3.87/1.00      | ~ m1_pre_topc(X0,X3)
% 3.87/1.00      | ~ m1_pre_topc(X3,X2)
% 3.87/1.00      | ~ r2_hidden(X4,X5)
% 3.87/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.87/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.87/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.87/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.87/1.00      | ~ v1_funct_1(sK4)
% 3.87/1.00      | v2_struct_0(X3)
% 3.87/1.00      | v2_struct_0(X1)
% 3.87/1.00      | v2_struct_0(X2)
% 3.87/1.00      | v2_struct_0(X0)
% 3.87/1.00      | ~ l1_pre_topc(X1)
% 3.87/1.00      | ~ l1_pre_topc(X2)
% 3.87/1.00      | ~ v2_pre_topc(X1)
% 3.87/1.00      | ~ v2_pre_topc(X2)
% 3.87/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.87/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_26,negated_conjecture,
% 3.87/1.00      ( v1_funct_1(sK4) ),
% 3.87/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_521,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.87/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.87/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.87/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.87/1.00      | ~ r2_hidden(X4,X5)
% 3.87/1.00      | ~ m1_pre_topc(X3,X2)
% 3.87/1.00      | ~ m1_pre_topc(X0,X3)
% 3.87/1.00      | ~ m1_pre_topc(X0,X2)
% 3.87/1.00      | ~ v3_pre_topc(X5,X3)
% 3.87/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.87/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.87/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.87/1.00      | v2_struct_0(X3)
% 3.87/1.00      | v2_struct_0(X1)
% 3.87/1.00      | v2_struct_0(X2)
% 3.87/1.00      | v2_struct_0(X0)
% 3.87/1.00      | ~ l1_pre_topc(X1)
% 3.87/1.00      | ~ l1_pre_topc(X2)
% 3.87/1.00      | ~ v2_pre_topc(X1)
% 3.87/1.00      | ~ v2_pre_topc(X2)
% 3.87/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_517,c_26]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_522,plain,
% 3.87/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.87/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.87/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.87/1.00      | ~ v3_pre_topc(X5,X3)
% 3.87/1.00      | ~ m1_pre_topc(X0,X2)
% 3.87/1.00      | ~ m1_pre_topc(X0,X3)
% 3.87/1.00      | ~ m1_pre_topc(X3,X2)
% 3.87/1.00      | ~ r2_hidden(X4,X5)
% 3.87/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.87/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.87/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.87/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.87/1.00      | v2_struct_0(X0)
% 3.87/1.00      | v2_struct_0(X1)
% 3.87/1.00      | v2_struct_0(X2)
% 3.87/1.00      | v2_struct_0(X3)
% 3.87/1.00      | ~ l1_pre_topc(X1)
% 3.87/1.00      | ~ l1_pre_topc(X2)
% 3.87/1.00      | ~ v2_pre_topc(X1)
% 3.87/1.00      | ~ v2_pre_topc(X2)
% 3.87/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.87/1.00      inference(renaming,[status(thm)],[c_521]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3,plain,
% 3.87/1.00      ( ~ r2_hidden(X0,X1)
% 3.87/1.00      | m1_subset_1(X0,X2)
% 3.87/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.87/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_15,plain,
% 3.87/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.87/1.00      | ~ m1_pre_topc(X2,X0)
% 3.87/1.00      | m1_pre_topc(X2,X1)
% 3.87/1.00      | ~ l1_pre_topc(X1)
% 3.87/1.00      | ~ v2_pre_topc(X1) ),
% 3.87/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_571,plain,
% 3.87/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.87/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.87/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.87/1.00      | ~ v3_pre_topc(X5,X3)
% 3.87/1.00      | ~ m1_pre_topc(X0,X3)
% 3.87/1.00      | ~ m1_pre_topc(X3,X2)
% 3.87/1.00      | ~ r2_hidden(X4,X5)
% 3.87/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.87/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.87/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.87/1.00      | v2_struct_0(X0)
% 3.87/1.00      | v2_struct_0(X1)
% 3.87/1.00      | v2_struct_0(X2)
% 3.87/1.00      | v2_struct_0(X3)
% 3.87/1.00      | ~ l1_pre_topc(X1)
% 3.87/1.00      | ~ l1_pre_topc(X2)
% 3.87/1.00      | ~ v2_pre_topc(X1)
% 3.87/1.00      | ~ v2_pre_topc(X2)
% 3.87/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.87/1.00      inference(forward_subsumption_resolution,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_522,c_3,c_15]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_595,plain,
% 3.87/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.87/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.87/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.87/1.01      | ~ m1_pre_topc(X0,X3)
% 3.87/1.01      | ~ m1_pre_topc(X3,X2)
% 3.87/1.01      | ~ r2_hidden(X4,X5)
% 3.87/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.87/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.87/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.87/1.01      | v2_struct_0(X3)
% 3.87/1.01      | v2_struct_0(X0)
% 3.87/1.01      | v2_struct_0(X2)
% 3.87/1.01      | v2_struct_0(X1)
% 3.87/1.01      | ~ l1_pre_topc(X6)
% 3.87/1.01      | ~ l1_pre_topc(X2)
% 3.87/1.01      | ~ l1_pre_topc(X1)
% 3.87/1.01      | ~ v2_pre_topc(X6)
% 3.87/1.01      | ~ v2_pre_topc(X2)
% 3.87/1.01      | ~ v2_pre_topc(X1)
% 3.87/1.01      | X3 != X6
% 3.87/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.01      | u1_struct_0(X3) != u1_struct_0(sK3)
% 3.87/1.01      | k2_struct_0(X6) != X5 ),
% 3.87/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_571]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_596,plain,
% 3.87/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.87/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.87/1.01      | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
% 3.87/1.01      | ~ m1_pre_topc(X0,X3)
% 3.87/1.01      | ~ m1_pre_topc(X3,X2)
% 3.87/1.01      | ~ r2_hidden(X4,k2_struct_0(X3))
% 3.87/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.87/1.01      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 3.87/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.87/1.01      | v2_struct_0(X0)
% 3.87/1.01      | v2_struct_0(X1)
% 3.87/1.01      | v2_struct_0(X2)
% 3.87/1.01      | v2_struct_0(X3)
% 3.87/1.01      | ~ l1_pre_topc(X1)
% 3.87/1.01      | ~ l1_pre_topc(X2)
% 3.87/1.01      | ~ l1_pre_topc(X3)
% 3.87/1.01      | ~ v2_pre_topc(X1)
% 3.87/1.01      | ~ v2_pre_topc(X2)
% 3.87/1.01      | ~ v2_pre_topc(X3)
% 3.87/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.87/1.01      inference(unflattening,[status(thm)],[c_595]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4,plain,
% 3.87/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.87/1.01      | ~ l1_pre_topc(X1)
% 3.87/1.01      | ~ v2_pre_topc(X1)
% 3.87/1.01      | v2_pre_topc(X0) ),
% 3.87/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_642,plain,
% 3.87/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.87/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.87/1.01      | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
% 3.87/1.01      | ~ m1_pre_topc(X0,X3)
% 3.87/1.01      | ~ m1_pre_topc(X3,X2)
% 3.87/1.01      | ~ r2_hidden(X4,k2_struct_0(X3))
% 3.87/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.87/1.01      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 3.87/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.87/1.01      | v2_struct_0(X0)
% 3.87/1.01      | v2_struct_0(X1)
% 3.87/1.01      | v2_struct_0(X2)
% 3.87/1.01      | v2_struct_0(X3)
% 3.87/1.01      | ~ l1_pre_topc(X1)
% 3.87/1.01      | ~ l1_pre_topc(X2)
% 3.87/1.01      | ~ v2_pre_topc(X1)
% 3.87/1.01      | ~ v2_pre_topc(X2)
% 3.87/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.87/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.87/1.01      inference(forward_subsumption_resolution,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_596,c_4,c_7]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2020,plain,
% 3.87/1.01      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.87/1.01      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.87/1.01      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
% 3.87/1.01      | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X2,X1) != iProver_top
% 3.87/1.01      | m1_pre_topc(X1,X3) != iProver_top
% 3.87/1.01      | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
% 3.87/1.01      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.87/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(X2) = iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X3) = iProver_top
% 3.87/1.01      | l1_pre_topc(X0) != iProver_top
% 3.87/1.01      | l1_pre_topc(X3) != iProver_top
% 3.87/1.01      | v2_pre_topc(X0) != iProver_top
% 3.87/1.01      | v2_pre_topc(X3) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2823,plain,
% 3.87/1.01      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.87/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.87/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.87/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.87/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(X2) = iProver_top
% 3.87/1.01      | v2_struct_0(sK1) = iProver_top
% 3.87/1.01      | l1_pre_topc(X2) != iProver_top
% 3.87/1.01      | l1_pre_topc(sK1) != iProver_top
% 3.87/1.01      | v2_pre_topc(X2) != iProver_top
% 3.87/1.01      | v2_pre_topc(sK1) != iProver_top ),
% 3.87/1.01      inference(equality_resolution,[status(thm)],[c_2020]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_33,negated_conjecture,
% 3.87/1.01      ( ~ v2_struct_0(sK1) ),
% 3.87/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_40,plain,
% 3.87/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_32,negated_conjecture,
% 3.87/1.01      ( v2_pre_topc(sK1) ),
% 3.87/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_41,plain,
% 3.87/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_31,negated_conjecture,
% 3.87/1.01      ( l1_pre_topc(sK1) ),
% 3.87/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_42,plain,
% 3.87/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5498,plain,
% 3.87/1.01      ( v2_pre_topc(X2) != iProver_top
% 3.87/1.01      | v2_struct_0(X2) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.87/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.87/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.87/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/1.01      | l1_pre_topc(X2) != iProver_top ),
% 3.87/1.01      inference(global_propositional_subsumption,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_2823,c_40,c_41,c_42]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5499,plain,
% 3.87/1.01      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.87/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.87/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.87/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.87/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(X2) = iProver_top
% 3.87/1.01      | l1_pre_topc(X2) != iProver_top
% 3.87/1.01      | v2_pre_topc(X2) != iProver_top ),
% 3.87/1.01      inference(renaming,[status(thm)],[c_5498]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2029,plain,
% 3.87/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2941,plain,
% 3.87/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_2029,c_2021]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5502,plain,
% 3.87/1.01      ( u1_struct_0(X0) != k2_struct_0(sK3)
% 3.87/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.87/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.87/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.87/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.87/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(X2) = iProver_top
% 3.87/1.01      | l1_pre_topc(X2) != iProver_top
% 3.87/1.01      | v2_pre_topc(X2) != iProver_top ),
% 3.87/1.01      inference(light_normalisation,[status(thm)],[c_5499,c_2941,c_3518]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5522,plain,
% 3.87/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.87/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.87/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.87/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.87/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(sK3) = iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top
% 3.87/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_3518,c_5502]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5601,plain,
% 3.87/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.87/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.87/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.87/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(sK3) = iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top
% 3.87/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.87/1.01      inference(light_normalisation,[status(thm)],[c_5522,c_3518]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_28,negated_conjecture,
% 3.87/1.01      ( ~ v2_struct_0(sK3) ),
% 3.87/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_45,plain,
% 3.87/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_24,negated_conjecture,
% 3.87/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.87/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2034,plain,
% 3.87/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_3323,plain,
% 3.87/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.87/1.01      inference(demodulation,[status(thm)],[c_2941,c_2034]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4144,plain,
% 3.87/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.87/1.01      inference(demodulation,[status(thm)],[c_3518,c_3323]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_17542,plain,
% 3.87/1.01      ( v2_struct_0(X0) = iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.87/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.87/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.87/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top
% 3.87/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.87/1.01      inference(global_propositional_subsumption,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_5601,c_45,c_4144]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_17543,plain,
% 3.87/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.87/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.87/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.87/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top
% 3.87/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.87/1.01      inference(renaming,[status(thm)],[c_17542]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_1,plain,
% 3.87/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.87/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2048,plain,
% 3.87/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_0,plain,
% 3.87/1.01      ( k2_subset_1(X0) = X0 ),
% 3.87/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2080,plain,
% 3.87/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.87/1.01      inference(light_normalisation,[status(thm)],[c_2048,c_0]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_17560,plain,
% 3.87/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.87/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.87/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.87/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.87/1.01      | v2_struct_0(X1) = iProver_top
% 3.87/1.01      | v2_struct_0(X0) = iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top
% 3.87/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.87/1.01      inference(forward_subsumption_resolution,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_17543,c_2080]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_17564,plain,
% 3.87/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.87/1.01      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 3.87/1.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.87/1.01      | v2_struct_0(sK0) = iProver_top
% 3.87/1.01      | v2_struct_0(sK2) = iProver_top
% 3.87/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.87/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_2095,c_17560]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_29,negated_conjecture,
% 3.87/1.01      ( m1_pre_topc(sK2,sK0) ),
% 3.87/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2031,plain,
% 3.87/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_3140,plain,
% 3.87/1.01      ( l1_pre_topc(sK0) != iProver_top
% 3.87/1.01      | l1_pre_topc(sK2) = iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_2031,c_2044]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_3520,plain,
% 3.87/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.87/1.01      inference(global_propositional_subsumption,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_3140,c_39]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_3525,plain,
% 3.87/1.01      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_3520,c_2021]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_17576,plain,
% 3.87/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.87/1.01      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.87/1.01      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 3.87/1.01      | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
% 3.87/1.01      | v2_struct_0(sK0) = iProver_top
% 3.87/1.01      | v2_struct_0(sK2) = iProver_top
% 3.87/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.87/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.87/1.01      inference(light_normalisation,[status(thm)],[c_17564,c_3525]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_14,plain,
% 3.87/1.01      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.87/1.01      | ~ m1_pre_topc(X0,X1)
% 3.87/1.01      | ~ l1_pre_topc(X1) ),
% 3.87/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2040,plain,
% 3.87/1.01      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.87/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4156,plain,
% 3.87/1.01      ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,X0) != iProver_top
% 3.87/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_3518,c_2040]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_6412,plain,
% 3.87/1.01      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
% 3.87/1.01      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.87/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_3525,c_4156]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_13,plain,
% 3.87/1.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.87/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2041,plain,
% 3.87/1.01      ( m1_pre_topc(X0,X0) = iProver_top
% 3.87/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_9,plain,
% 3.87/1.01      ( m1_pre_topc(X0,X1)
% 3.87/1.01      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/1.01      | ~ l1_pre_topc(X0)
% 3.87/1.01      | ~ l1_pre_topc(X1) ),
% 3.87/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2043,plain,
% 3.87/1.01      ( m1_pre_topc(X0,X1) = iProver_top
% 3.87/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top
% 3.87/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4685,plain,
% 3.87/1.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK2) = iProver_top
% 3.87/1.01      | l1_pre_topc(X0) != iProver_top
% 3.87/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_3525,c_2043]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_23,negated_conjecture,
% 3.87/1.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.87/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4359,plain,
% 3.87/1.01      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.87/1.01      inference(demodulation,[status(thm)],[c_3525,c_23]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4717,plain,
% 3.87/1.01      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | l1_pre_topc(X0) != iProver_top
% 3.87/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/1.01      inference(light_normalisation,[status(thm)],[c_4685,c_4359]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5101,plain,
% 3.87/1.01      ( l1_pre_topc(X0) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.87/1.01      inference(global_propositional_subsumption,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_4717,c_39,c_3140]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5102,plain,
% 3.87/1.01      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.87/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.87/1.01      inference(renaming,[status(thm)],[c_5101]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5110,plain,
% 3.87/1.01      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.87/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_2041,c_5102]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_10,plain,
% 3.87/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.87/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/1.01      | ~ l1_pre_topc(X0)
% 3.87/1.01      | ~ l1_pre_topc(X1) ),
% 3.87/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_191,plain,
% 3.87/1.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/1.01      | ~ m1_pre_topc(X0,X1)
% 3.87/1.01      | ~ l1_pre_topc(X1) ),
% 3.87/1.01      inference(global_propositional_subsumption,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_10,c_7]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_192,plain,
% 3.87/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.87/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.87/1.01      | ~ l1_pre_topc(X1) ),
% 3.87/1.01      inference(renaming,[status(thm)],[c_191]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2023,plain,
% 3.87/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.87/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4624,plain,
% 3.87/1.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK2) != iProver_top
% 3.87/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_3525,c_2023]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4661,plain,
% 3.87/1.01      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) = iProver_top
% 3.87/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/1.01      inference(light_normalisation,[status(thm)],[c_4624,c_4359]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4995,plain,
% 3.87/1.01      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.87/1.01      inference(global_propositional_subsumption,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_4661,c_39,c_3140]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4996,plain,
% 3.87/1.01      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.87/1.01      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.87/1.01      inference(renaming,[status(thm)],[c_4995]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_5003,plain,
% 3.87/1.01      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.87/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_2041,c_4996]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_21,negated_conjecture,
% 3.87/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.87/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2036,plain,
% 3.87/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2075,plain,
% 3.87/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.87/1.01      inference(light_normalisation,[status(thm)],[c_2036,c_20]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4358,plain,
% 3.87/1.01      ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
% 3.87/1.01      inference(demodulation,[status(thm)],[c_3525,c_2075]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_22,negated_conjecture,
% 3.87/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.87/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2035,plain,
% 3.87/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2,plain,
% 3.87/1.01      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.87/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2047,plain,
% 3.87/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.87/1.01      | m1_subset_1(X0,X1) != iProver_top
% 3.87/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_3155,plain,
% 3.87/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.87/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/1.01      inference(superposition,[status(thm)],[c_2035,c_2047]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_50,plain,
% 3.87/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2338,plain,
% 3.87/1.01      ( r2_hidden(sK5,u1_struct_0(sK3))
% 3.87/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.87/1.01      | v1_xboole_0(u1_struct_0(sK3)) ),
% 3.87/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2339,plain,
% 3.87/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.87/1.01      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.87/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_2338]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_8,plain,
% 3.87/1.01      ( v2_struct_0(X0)
% 3.87/1.01      | ~ l1_struct_0(X0)
% 3.87/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.87/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_385,plain,
% 3.87/1.01      ( v2_struct_0(X0)
% 3.87/1.01      | ~ l1_pre_topc(X0)
% 3.87/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.87/1.01      inference(resolution,[status(thm)],[c_6,c_8]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2429,plain,
% 3.87/1.01      ( v2_struct_0(sK3)
% 3.87/1.01      | ~ l1_pre_topc(sK3)
% 3.87/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.87/1.01      inference(instantiation,[status(thm)],[c_385]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_2430,plain,
% 3.87/1.01      ( v2_struct_0(sK3) = iProver_top
% 3.87/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.87/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_3584,plain,
% 3.87/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.87/1.01      inference(global_propositional_subsumption,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_3155,c_39,c_45,c_50,c_2339,c_2430,c_3139]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_4143,plain,
% 3.87/1.01      ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.87/1.01      inference(demodulation,[status(thm)],[c_3518,c_3584]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_18,negated_conjecture,
% 3.87/1.01      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.87/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_53,plain,
% 3.87/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_46,plain,
% 3.87/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_30,negated_conjecture,
% 3.87/1.01      ( ~ v2_struct_0(sK2) ),
% 3.87/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_43,plain,
% 3.87/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_35,negated_conjecture,
% 3.87/1.01      ( v2_pre_topc(sK0) ),
% 3.87/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_38,plain,
% 3.87/1.01      ( v2_pre_topc(sK0) = iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_36,negated_conjecture,
% 3.87/1.01      ( ~ v2_struct_0(sK0) ),
% 3.87/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(c_37,plain,
% 3.87/1.01      ( v2_struct_0(sK0) != iProver_top ),
% 3.87/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.87/1.01  
% 3.87/1.01  cnf(contradiction,plain,
% 3.87/1.01      ( $false ),
% 3.87/1.01      inference(minisat,
% 3.87/1.01                [status(thm)],
% 3.87/1.01                [c_17576,c_6412,c_5110,c_5003,c_4358,c_4143,c_3140,
% 3.87/1.01                 c_3139,c_53,c_46,c_43,c_39,c_38,c_37]) ).
% 3.87/1.01  
% 3.87/1.01  
% 3.87/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/1.01  
% 3.87/1.01  ------                               Statistics
% 3.87/1.01  
% 3.87/1.01  ------ General
% 3.87/1.01  
% 3.87/1.01  abstr_ref_over_cycles:                  0
% 3.87/1.01  abstr_ref_under_cycles:                 0
% 3.87/1.01  gc_basic_clause_elim:                   0
% 3.87/1.01  forced_gc_time:                         0
% 3.87/1.01  parsing_time:                           0.025
% 3.87/1.01  unif_index_cands_time:                  0.
% 3.87/1.01  unif_index_add_time:                    0.
% 3.87/1.01  orderings_time:                         0.
% 3.87/1.01  out_proof_time:                         0.013
% 3.87/1.01  total_time:                             0.508
% 3.87/1.01  num_of_symbols:                         59
% 3.87/1.01  num_of_terms:                           9437
% 3.87/1.01  
% 3.87/1.01  ------ Preprocessing
% 3.87/1.01  
% 3.87/1.01  num_of_splits:                          0
% 3.87/1.01  num_of_split_atoms:                     0
% 3.87/1.01  num_of_reused_defs:                     0
% 3.87/1.01  num_eq_ax_congr_red:                    12
% 3.87/1.01  num_of_sem_filtered_clauses:            1
% 3.87/1.01  num_of_subtypes:                        0
% 3.87/1.01  monotx_restored_types:                  0
% 3.87/1.01  sat_num_of_epr_types:                   0
% 3.87/1.01  sat_num_of_non_cyclic_types:            0
% 3.87/1.01  sat_guarded_non_collapsed_types:        0
% 3.87/1.01  num_pure_diseq_elim:                    0
% 3.87/1.01  simp_replaced_by:                       0
% 3.87/1.01  res_preprocessed:                       171
% 3.87/1.01  prep_upred:                             0
% 3.87/1.01  prep_unflattend:                        17
% 3.87/1.01  smt_new_axioms:                         0
% 3.87/1.01  pred_elim_cands:                        9
% 3.87/1.01  pred_elim:                              4
% 3.87/1.01  pred_elim_cl:                           4
% 3.87/1.01  pred_elim_cycles:                       11
% 3.87/1.01  merged_defs:                            0
% 3.87/1.01  merged_defs_ncl:                        0
% 3.87/1.01  bin_hyper_res:                          0
% 3.87/1.01  prep_cycles:                            4
% 3.87/1.01  pred_elim_time:                         0.038
% 3.87/1.01  splitting_time:                         0.
% 3.87/1.01  sem_filter_time:                        0.
% 3.87/1.01  monotx_time:                            0.001
% 3.87/1.01  subtype_inf_time:                       0.
% 3.87/1.01  
% 3.87/1.01  ------ Problem properties
% 3.87/1.01  
% 3.87/1.01  clauses:                                33
% 3.87/1.01  conjectures:                            17
% 3.87/1.01  epr:                                    17
% 3.87/1.01  horn:                                   30
% 3.87/1.01  ground:                                 17
% 3.87/1.01  unary:                                  19
% 3.87/1.01  binary:                                 2
% 3.87/1.01  lits:                                   95
% 3.87/1.01  lits_eq:                                8
% 3.87/1.01  fd_pure:                                0
% 3.87/1.01  fd_pseudo:                              0
% 3.87/1.01  fd_cond:                                0
% 3.87/1.01  fd_pseudo_cond:                         0
% 3.87/1.01  ac_symbols:                             0
% 3.87/1.01  
% 3.87/1.01  ------ Propositional Solver
% 3.87/1.01  
% 3.87/1.01  prop_solver_calls:                      32
% 3.87/1.01  prop_fast_solver_calls:                 2646
% 3.87/1.01  smt_solver_calls:                       0
% 3.87/1.01  smt_fast_solver_calls:                  0
% 3.87/1.01  prop_num_of_clauses:                    5831
% 3.87/1.01  prop_preprocess_simplified:             10612
% 3.87/1.01  prop_fo_subsumed:                       112
% 3.87/1.01  prop_solver_time:                       0.
% 3.87/1.01  smt_solver_time:                        0.
% 3.87/1.01  smt_fast_solver_time:                   0.
% 3.87/1.01  prop_fast_solver_time:                  0.
% 3.87/1.01  prop_unsat_core_time:                   0.
% 3.87/1.01  
% 3.87/1.01  ------ QBF
% 3.87/1.01  
% 3.87/1.01  qbf_q_res:                              0
% 3.87/1.01  qbf_num_tautologies:                    0
% 3.87/1.01  qbf_prep_cycles:                        0
% 3.87/1.01  
% 3.87/1.01  ------ BMC1
% 3.87/1.01  
% 3.87/1.01  bmc1_current_bound:                     -1
% 3.87/1.01  bmc1_last_solved_bound:                 -1
% 3.87/1.01  bmc1_unsat_core_size:                   -1
% 3.87/1.01  bmc1_unsat_core_parents_size:           -1
% 3.87/1.01  bmc1_merge_next_fun:                    0
% 3.87/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.87/1.01  
% 3.87/1.01  ------ Instantiation
% 3.87/1.01  
% 3.87/1.01  inst_num_of_clauses:                    1837
% 3.87/1.01  inst_num_in_passive:                    727
% 3.87/1.01  inst_num_in_active:                     967
% 3.87/1.01  inst_num_in_unprocessed:                143
% 3.87/1.01  inst_num_of_loops:                      1000
% 3.87/1.01  inst_num_of_learning_restarts:          0
% 3.87/1.01  inst_num_moves_active_passive:          28
% 3.87/1.01  inst_lit_activity:                      0
% 3.87/1.01  inst_lit_activity_moves:                0
% 3.87/1.01  inst_num_tautologies:                   0
% 3.87/1.01  inst_num_prop_implied:                  0
% 3.87/1.01  inst_num_existing_simplified:           0
% 3.87/1.01  inst_num_eq_res_simplified:             0
% 3.87/1.01  inst_num_child_elim:                    0
% 3.87/1.01  inst_num_of_dismatching_blockings:      948
% 3.87/1.01  inst_num_of_non_proper_insts:           2315
% 3.87/1.01  inst_num_of_duplicates:                 0
% 3.87/1.01  inst_inst_num_from_inst_to_res:         0
% 3.87/1.01  inst_dismatching_checking_time:         0.
% 3.87/1.01  
% 3.87/1.01  ------ Resolution
% 3.87/1.01  
% 3.87/1.01  res_num_of_clauses:                     0
% 3.87/1.01  res_num_in_passive:                     0
% 3.87/1.01  res_num_in_active:                      0
% 3.87/1.01  res_num_of_loops:                       175
% 3.87/1.01  res_forward_subset_subsumed:            221
% 3.87/1.01  res_backward_subset_subsumed:           0
% 3.87/1.01  res_forward_subsumed:                   0
% 3.87/1.01  res_backward_subsumed:                  0
% 3.87/1.01  res_forward_subsumption_resolution:     8
% 3.87/1.01  res_backward_subsumption_resolution:    0
% 3.87/1.01  res_clause_to_clause_subsumption:       1392
% 3.87/1.01  res_orphan_elimination:                 0
% 3.87/1.01  res_tautology_del:                      304
% 3.87/1.01  res_num_eq_res_simplified:              0
% 3.87/1.01  res_num_sel_changes:                    0
% 3.87/1.01  res_moves_from_active_to_pass:          0
% 3.87/1.01  
% 3.87/1.01  ------ Superposition
% 3.87/1.01  
% 3.87/1.01  sup_time_total:                         0.
% 3.87/1.01  sup_time_generating:                    0.
% 3.87/1.01  sup_time_sim_full:                      0.
% 3.87/1.01  sup_time_sim_immed:                     0.
% 3.87/1.01  
% 3.87/1.01  sup_num_of_clauses:                     243
% 3.87/1.01  sup_num_in_active:                      188
% 3.87/1.01  sup_num_in_passive:                     55
% 3.87/1.01  sup_num_of_loops:                       198
% 3.87/1.01  sup_fw_superposition:                   240
% 3.87/1.01  sup_bw_superposition:                   170
% 3.87/1.01  sup_immediate_simplified:               137
% 3.87/1.01  sup_given_eliminated:                   0
% 3.87/1.01  comparisons_done:                       0
% 3.87/1.01  comparisons_avoided:                    0
% 3.87/1.01  
% 3.87/1.01  ------ Simplifications
% 3.87/1.01  
% 3.87/1.01  
% 3.87/1.01  sim_fw_subset_subsumed:                 57
% 3.87/1.01  sim_bw_subset_subsumed:                 24
% 3.87/1.01  sim_fw_subsumed:                        36
% 3.87/1.01  sim_bw_subsumed:                        0
% 3.87/1.01  sim_fw_subsumption_res:                 10
% 3.87/1.01  sim_bw_subsumption_res:                 0
% 3.87/1.01  sim_tautology_del:                      27
% 3.87/1.01  sim_eq_tautology_del:                   0
% 3.87/1.01  sim_eq_res_simp:                        0
% 3.87/1.01  sim_fw_demodulated:                     0
% 3.87/1.01  sim_bw_demodulated:                     10
% 3.87/1.01  sim_light_normalised:                   67
% 3.87/1.01  sim_joinable_taut:                      0
% 3.87/1.01  sim_joinable_simp:                      0
% 3.87/1.01  sim_ac_normalised:                      0
% 3.87/1.01  sim_smt_subsumption:                    0
% 3.87/1.01  
%------------------------------------------------------------------------------
