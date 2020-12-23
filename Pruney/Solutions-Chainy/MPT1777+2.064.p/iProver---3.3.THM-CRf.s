%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:38 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 774 expanded)
%              Number of clauses        :  100 ( 166 expanded)
%              Number of leaves         :   22 ( 341 expanded)
%              Depth                    :   15
%              Number of atoms          :  872 (10599 expanded)
%              Number of equality atoms :  226 (1579 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f36,f49,f48,f47,f46,f45,f44,f43])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f50])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f28])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f55,plain,(
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

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

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
    inference(cnf_transformation,[],[f42])).

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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1137,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1147,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1147,c_0])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1139,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3181,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1139])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1865,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_5,c_32])).

cnf(c_1866,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_1122,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1146,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3015,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1146])).

cnf(c_3351,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3181,c_41,c_42,c_1866,c_3015])).

cnf(c_3361,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2) != iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_3351])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_40,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_44,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_45,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_46,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_49,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_50,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_56,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1129,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1176,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1129,c_23])).

cnf(c_1863,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_30])).

cnf(c_1864,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1863])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_287,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_288,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_287])).

cnf(c_2710,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_2711,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2710])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1135,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_274,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_5])).

cnf(c_275,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_1114,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_1678,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1114])).

cnf(c_2862,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1678,c_42,c_1866])).

cnf(c_2863,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_2862])).

cnf(c_2870,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_2863])).

cnf(c_1124,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3014,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_1146])).

cnf(c_1120,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1144,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2391,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1144])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1145,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3976,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2391,c_1145])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1127,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4163,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3976,c_1127])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1126,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4164,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3976,c_1126])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1130,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1202,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1130,c_23])).

cnf(c_19,plain,
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
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1133,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1134,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1372,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1133,c_1134])).

cnf(c_4842,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1372])).

cnf(c_4860,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4842,c_3976])).

cnf(c_6289,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3361,c_40,c_41,c_42,c_43,c_44,c_45,c_46,c_48,c_49,c_50,c_53,c_56,c_1176,c_1864,c_1866,c_2711,c_2870,c_3014,c_4163,c_4164,c_4860])).

cnf(c_1143,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2761,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1143])).

cnf(c_5349,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2761,c_42,c_1866])).

cnf(c_5354,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5349,c_1144])).

cnf(c_5358,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_5354,c_1145])).

cnf(c_6293,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6289,c_5358])).

cnf(c_6296,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_6293])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6296,c_3015,c_1866,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:52:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.99  
% 3.18/0.99  ------  iProver source info
% 3.18/0.99  
% 3.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.99  git: non_committed_changes: false
% 3.18/0.99  git: last_make_outside_of_git: false
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             sel
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         604.99
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              none
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           false
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             false
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     num_symb
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       true
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  ------ Parsing...
% 3.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.99  ------ Proving...
% 3.18/0.99  ------ Problem Properties 
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  clauses                                 39
% 3.18/0.99  conjectures                             19
% 3.18/0.99  EPR                                     18
% 3.18/0.99  Horn                                    37
% 3.18/0.99  unary                                   21
% 3.18/0.99  binary                                  3
% 3.18/0.99  lits                                    120
% 3.18/0.99  lits eq                                 4
% 3.18/0.99  fd_pure                                 0
% 3.18/0.99  fd_pseudo                               0
% 3.18/0.99  fd_cond                                 0
% 3.18/0.99  fd_pseudo_cond                          0
% 3.18/0.99  AC symbols                              0
% 3.18/0.99  
% 3.18/0.99  ------ Input Options Time Limit: Unbounded
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  Current options:
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             sel
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         604.99
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              none
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           false
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             false
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     num_symb
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       true
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ Proving...
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS status Theorem for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  fof(f9,axiom,(
% 3.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f25,plain,(
% 3.18/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f9])).
% 3.18/0.99  
% 3.18/0.99  fof(f26,plain,(
% 3.18/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f25])).
% 3.18/0.99  
% 3.18/0.99  fof(f63,plain,(
% 3.18/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f26])).
% 3.18/0.99  
% 3.18/0.99  fof(f2,axiom,(
% 3.18/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f52,plain,(
% 3.18/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f2])).
% 3.18/0.99  
% 3.18/0.99  fof(f1,axiom,(
% 3.18/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f51,plain,(
% 3.18/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.18/0.99    inference(cnf_transformation,[],[f1])).
% 3.18/0.99  
% 3.18/0.99  fof(f15,conjecture,(
% 3.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f16,negated_conjecture,(
% 3.18/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.18/0.99    inference(negated_conjecture,[],[f15])).
% 3.18/0.99  
% 3.18/0.99  fof(f35,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f16])).
% 3.18/0.99  
% 3.18/0.99  fof(f36,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.18/0.99    inference(flattening,[],[f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f49,plain,(
% 3.18/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f48,plain,(
% 3.18/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f47,plain,(
% 3.18/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f46,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f45,plain,(
% 3.18/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f44,plain,(
% 3.18/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f43,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f50,plain,(
% 3.18/0.99    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f36,f49,f48,f47,f46,f45,f44,f43])).
% 3.18/0.99  
% 3.18/0.99  fof(f85,plain,(
% 3.18/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f7,axiom,(
% 3.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f22,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f7])).
% 3.18/0.99  
% 3.18/0.99  fof(f23,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f22])).
% 3.18/0.99  
% 3.18/0.99  fof(f37,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f23])).
% 3.18/0.99  
% 3.18/0.99  fof(f38,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f37])).
% 3.18/0.99  
% 3.18/0.99  fof(f57,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f38])).
% 3.18/0.99  
% 3.18/0.99  fof(f73,plain,(
% 3.18/0.99    v2_pre_topc(sK0)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f74,plain,(
% 3.18/0.99    l1_pre_topc(sK0)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f6,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f21,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f6])).
% 3.18/0.99  
% 3.18/0.99  fof(f56,plain,(
% 3.18/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f21])).
% 3.18/0.99  
% 3.18/0.99  fof(f79,plain,(
% 3.18/0.99    m1_pre_topc(sK2,sK0)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f3,axiom,(
% 3.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f17,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f3])).
% 3.18/0.99  
% 3.18/0.99  fof(f18,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f17])).
% 3.18/0.99  
% 3.18/0.99  fof(f53,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f18])).
% 3.18/0.99  
% 3.18/0.99  fof(f72,plain,(
% 3.18/0.99    ~v2_struct_0(sK0)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f75,plain,(
% 3.18/0.99    ~v2_struct_0(sK1)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f76,plain,(
% 3.18/0.99    v2_pre_topc(sK1)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f77,plain,(
% 3.18/0.99    l1_pre_topc(sK1)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f78,plain,(
% 3.18/0.99    ~v2_struct_0(sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f80,plain,(
% 3.18/0.99    ~v2_struct_0(sK3)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f81,plain,(
% 3.18/0.99    m1_pre_topc(sK3,sK0)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f82,plain,(
% 3.18/0.99    v1_funct_1(sK4)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f86,plain,(
% 3.18/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f90,plain,(
% 3.18/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f87,plain,(
% 3.18/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f88,plain,(
% 3.18/0.99    sK5 = sK6),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f10,axiom,(
% 3.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f27,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f10])).
% 3.18/0.99  
% 3.18/0.99  fof(f28,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f27])).
% 3.18/0.99  
% 3.18/0.99  fof(f40,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f28])).
% 3.18/0.99  
% 3.18/0.99  fof(f41,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f65,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f41])).
% 3.18/0.99  
% 3.18/0.99  fof(f92,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.99    inference(equality_resolution,[],[f65])).
% 3.18/0.99  
% 3.18/0.99  fof(f11,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f29,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f11])).
% 3.18/0.99  
% 3.18/0.99  fof(f67,plain,(
% 3.18/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f29])).
% 3.18/0.99  
% 3.18/0.99  fof(f12,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f30,plain,(
% 3.18/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f12])).
% 3.18/0.99  
% 3.18/0.99  fof(f68,plain,(
% 3.18/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f30])).
% 3.18/0.99  
% 3.18/0.99  fof(f8,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f24,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f8])).
% 3.18/0.99  
% 3.18/0.99  fof(f39,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f24])).
% 3.18/0.99  
% 3.18/0.99  fof(f61,plain,(
% 3.18/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f5,axiom,(
% 3.18/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f20,plain,(
% 3.18/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f5])).
% 3.18/0.99  
% 3.18/0.99  fof(f55,plain,(
% 3.18/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f20])).
% 3.18/0.99  
% 3.18/0.99  fof(f4,axiom,(
% 3.18/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f19,plain,(
% 3.18/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f4])).
% 3.18/0.99  
% 3.18/0.99  fof(f54,plain,(
% 3.18/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f19])).
% 3.18/0.99  
% 3.18/0.99  fof(f84,plain,(
% 3.18/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f83,plain,(
% 3.18/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f89,plain,(
% 3.18/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.18/0.99    inference(cnf_transformation,[],[f50])).
% 3.18/0.99  
% 3.18/0.99  fof(f14,axiom,(
% 3.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f33,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f14])).
% 3.18/0.99  
% 3.18/0.99  fof(f34,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.18/0.99    inference(flattening,[],[f33])).
% 3.18/0.99  
% 3.18/0.99  fof(f42,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f34])).
% 3.18/0.99  
% 3.18/0.99  fof(f71,plain,(
% 3.18/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f42])).
% 3.18/0.99  
% 3.18/0.99  fof(f94,plain,(
% 3.18/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.99    inference(equality_resolution,[],[f71])).
% 3.18/0.99  
% 3.18/0.99  fof(f13,axiom,(
% 3.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f31,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f13])).
% 3.18/0.99  
% 3.18/0.99  fof(f32,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.99    inference(flattening,[],[f31])).
% 3.18/0.99  
% 3.18/0.99  fof(f69,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f32])).
% 3.18/0.99  
% 3.18/0.99  cnf(c_12,plain,
% 3.18/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.18/0.99      | ~ l1_pre_topc(X0)
% 3.18/0.99      | ~ v2_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1137,plain,
% 3.18/0.99      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 3.18/0.99      | l1_pre_topc(X0) != iProver_top
% 3.18/0.99      | v2_pre_topc(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1,plain,
% 3.18/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1147,plain,
% 3.18/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_0,plain,
% 3.18/0.99      ( k2_subset_1(X0) = X0 ),
% 3.18/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1181,plain,
% 3.18/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_1147,c_0]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_26,negated_conjecture,
% 3.18/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.18/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_9,plain,
% 3.18/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.18/0.99      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X1)
% 3.18/0.99      | ~ v2_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1139,plain,
% 3.18/0.99      ( v3_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.18/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top
% 3.18/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3181,plain,
% 3.18/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.18/0.99      | v3_pre_topc(X0,sK3) = iProver_top
% 3.18/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_26,c_1139]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_38,negated_conjecture,
% 3.18/0.99      ( v2_pre_topc(sK0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_41,plain,
% 3.18/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_37,negated_conjecture,
% 3.18/0.99      ( l1_pre_topc(sK0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_42,plain,
% 3.18/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_32,negated_conjecture,
% 3.18/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1865,plain,
% 3.18/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.18/0.99      inference(resolution,[status(thm)],[c_5,c_32]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1866,plain,
% 3.18/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1122,plain,
% 3.18/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1)
% 3.18/0.99      | ~ v2_pre_topc(X1)
% 3.18/0.99      | v2_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1146,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top
% 3.18/0.99      | v2_pre_topc(X1) != iProver_top
% 3.18/0.99      | v2_pre_topc(X0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3015,plain,
% 3.18/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK2) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1122,c_1146]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3351,plain,
% 3.18/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.18/0.99      | v3_pre_topc(X0,sK3) = iProver_top
% 3.18/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3181,c_41,c_42,c_1866,c_3015]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3361,plain,
% 3.18/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK2) != iProver_top
% 3.18/0.99      | v3_pre_topc(u1_struct_0(sK2),sK3) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1181,c_3351]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_39,negated_conjecture,
% 3.18/0.99      ( ~ v2_struct_0(sK0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_40,plain,
% 3.18/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_36,negated_conjecture,
% 3.18/0.99      ( ~ v2_struct_0(sK1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_43,plain,
% 3.18/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_35,negated_conjecture,
% 3.18/0.99      ( v2_pre_topc(sK1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_44,plain,
% 3.18/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_34,negated_conjecture,
% 3.18/0.99      ( l1_pre_topc(sK1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_45,plain,
% 3.18/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_33,negated_conjecture,
% 3.18/0.99      ( ~ v2_struct_0(sK2) ),
% 3.18/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_46,plain,
% 3.18/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_31,negated_conjecture,
% 3.18/0.99      ( ~ v2_struct_0(sK3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_48,plain,
% 3.18/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_30,negated_conjecture,
% 3.18/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_49,plain,
% 3.18/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_29,negated_conjecture,
% 3.18/0.99      ( v1_funct_1(sK4) ),
% 3.18/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_50,plain,
% 3.18/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_25,negated_conjecture,
% 3.18/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_53,plain,
% 3.18/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_21,negated_conjecture,
% 3.18/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.18/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_56,plain,
% 3.18/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_24,negated_conjecture,
% 3.18/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1129,plain,
% 3.18/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_23,negated_conjecture,
% 3.18/0.99      ( sK5 = sK6 ),
% 3.18/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1176,plain,
% 3.18/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_1129,c_23]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1863,plain,
% 3.18/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.18/0.99      inference(resolution,[status(thm)],[c_5,c_30]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1864,plain,
% 3.18/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1863]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_14,plain,
% 3.18/0.99      ( v1_tsep_1(X0,X1)
% 3.18/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.18/0.99      | ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X1)
% 3.18/0.99      | ~ v2_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_16,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_287,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.18/0.99      | v1_tsep_1(X0,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1)
% 3.18/0.99      | ~ v2_pre_topc(X1) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_14,c_16]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_288,plain,
% 3.18/0.99      ( v1_tsep_1(X0,X1)
% 3.18/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.18/0.99      | ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1)
% 3.18/0.99      | ~ v2_pre_topc(X1) ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_287]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2710,plain,
% 3.18/0.99      ( v1_tsep_1(sK2,sK3)
% 3.18/0.99      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.18/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.18/0.99      | ~ l1_pre_topc(sK3)
% 3.18/0.99      | ~ v2_pre_topc(sK3) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_288]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2711,plain,
% 3.18/0.99      ( v1_tsep_1(sK2,sK3) = iProver_top
% 3.18/0.99      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 3.18/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_2710]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_17,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1135,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.18/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_11,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X0)
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_274,plain,
% 3.18/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_11,c_5]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_275,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.18/0.99      | ~ l1_pre_topc(X1) ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_274]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1114,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1678,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK3) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_26,c_1114]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2862,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1678,c_42,c_1866]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2863,plain,
% 3.18/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_2862]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2870,plain,
% 3.18/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1135,c_2863]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1124,plain,
% 3.18/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3014,plain,
% 3.18/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK3) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1124,c_1146]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1120,plain,
% 3.18/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4,plain,
% 3.18/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1144,plain,
% 3.18/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2391,plain,
% 3.18/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1120,c_1144]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3,plain,
% 3.18/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1145,plain,
% 3.18/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.18/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3976,plain,
% 3.18/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_2391,c_1145]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_27,negated_conjecture,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1127,plain,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4163,plain,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_3976,c_1127]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_28,negated_conjecture,
% 3.18/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1126,plain,
% 3.18/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4164,plain,
% 3.18/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_3976,c_1126]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_22,negated_conjecture,
% 3.18/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.18/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1130,plain,
% 3.18/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1202,plain,
% 3.18/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_1130,c_23]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_19,plain,
% 3.18/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.18/0.99      | ~ v1_tsep_1(X4,X0)
% 3.18/0.99      | ~ m1_pre_topc(X4,X5)
% 3.18/0.99      | ~ m1_pre_topc(X4,X0)
% 3.18/0.99      | ~ m1_pre_topc(X0,X5)
% 3.18/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.99      | v2_struct_0(X5)
% 3.18/0.99      | v2_struct_0(X1)
% 3.18/0.99      | v2_struct_0(X4)
% 3.18/0.99      | v2_struct_0(X0)
% 3.18/0.99      | ~ v1_funct_1(X2)
% 3.18/0.99      | ~ l1_pre_topc(X5)
% 3.18/0.99      | ~ l1_pre_topc(X1)
% 3.18/0.99      | ~ v2_pre_topc(X5)
% 3.18/0.99      | ~ v2_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1133,plain,
% 3.18/0.99      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.18/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.18/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.18/0.99      | v1_tsep_1(X4,X0) != iProver_top
% 3.18/0.99      | m1_pre_topc(X4,X5) != iProver_top
% 3.18/0.99      | m1_pre_topc(X4,X0) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,X5) != iProver_top
% 3.18/0.99      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.18/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.18/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.18/0.99      | v2_struct_0(X5) = iProver_top
% 3.18/0.99      | v2_struct_0(X1) = iProver_top
% 3.18/0.99      | v2_struct_0(X4) = iProver_top
% 3.18/0.99      | v2_struct_0(X0) = iProver_top
% 3.18/0.99      | v1_funct_1(X2) != iProver_top
% 3.18/0.99      | l1_pre_topc(X5) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top
% 3.18/0.99      | v2_pre_topc(X5) != iProver_top
% 3.18/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_18,plain,
% 3.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.99      | ~ m1_pre_topc(X2,X0)
% 3.18/0.99      | m1_pre_topc(X2,X1)
% 3.18/0.99      | ~ l1_pre_topc(X1)
% 3.18/0.99      | ~ v2_pre_topc(X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1134,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.18/0.99      | m1_pre_topc(X2,X1) = iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top
% 3.18/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1372,plain,
% 3.18/0.99      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.18/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.18/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.18/0.99      | v1_tsep_1(X4,X0) != iProver_top
% 3.18/0.99      | m1_pre_topc(X4,X0) != iProver_top
% 3.18/0.99      | m1_pre_topc(X0,X5) != iProver_top
% 3.18/0.99      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.18/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.18/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.18/0.99      | v2_struct_0(X5) = iProver_top
% 3.18/0.99      | v2_struct_0(X1) = iProver_top
% 3.18/0.99      | v2_struct_0(X4) = iProver_top
% 3.18/0.99      | v2_struct_0(X0) = iProver_top
% 3.18/0.99      | v1_funct_1(X2) != iProver_top
% 3.18/0.99      | l1_pre_topc(X5) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top
% 3.18/0.99      | v2_pre_topc(X5) != iProver_top
% 3.18/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.18/0.99      inference(forward_subsumption_resolution,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1133,c_1134]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4842,plain,
% 3.18/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.18/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.18/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.18/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.18/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.18/0.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.18/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.18/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.18/0.99      | v2_struct_0(sK0) = iProver_top
% 3.18/0.99      | v2_struct_0(sK2) = iProver_top
% 3.18/0.99      | v2_struct_0(sK1) = iProver_top
% 3.18/0.99      | v2_struct_0(sK3) = iProver_top
% 3.18/0.99      | v1_funct_1(sK4) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1202,c_1372]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4860,plain,
% 3.18/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.18/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
% 3.18/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.18/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.18/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.18/0.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.18/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.18/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.18/0.99      | v2_struct_0(sK0) = iProver_top
% 3.18/0.99      | v2_struct_0(sK2) = iProver_top
% 3.18/0.99      | v2_struct_0(sK1) = iProver_top
% 3.18/0.99      | v2_struct_0(sK3) = iProver_top
% 3.18/0.99      | v1_funct_1(sK4) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_4842,c_3976]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6289,plain,
% 3.18/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK2) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3361,c_40,c_41,c_42,c_43,c_44,c_45,c_46,c_48,c_49,
% 3.18/0.99                 c_50,c_53,c_56,c_1176,c_1864,c_1866,c_2711,c_2870,
% 3.18/0.99                 c_3014,c_4163,c_4164,c_4860]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1143,plain,
% 3.18/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.99      | l1_pre_topc(X1) != iProver_top
% 3.18/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2761,plain,
% 3.18/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.18/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1122,c_1143]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5349,plain,
% 3.18/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2761,c_42,c_1866]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5354,plain,
% 3.18/0.99      ( l1_struct_0(sK2) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_5349,c_1144]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5358,plain,
% 3.18/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_5354,c_1145]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6293,plain,
% 3.18/0.99      ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_6289,c_5358]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6296,plain,
% 3.18/0.99      ( l1_pre_topc(sK2) != iProver_top
% 3.18/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1137,c_6293]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(contradiction,plain,
% 3.18/0.99      ( $false ),
% 3.18/0.99      inference(minisat,[status(thm)],[c_6296,c_3015,c_1866,c_42,c_41]) ).
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  ------                               Statistics
% 3.18/0.99  
% 3.18/0.99  ------ Selected
% 3.18/0.99  
% 3.18/0.99  total_time:                             0.305
% 3.18/0.99  
%------------------------------------------------------------------------------
