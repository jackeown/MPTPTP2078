%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:40 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 731 expanded)
%              Number of clauses        :  132 ( 201 expanded)
%              Number of leaves         :   25 ( 301 expanded)
%              Depth                    :   24
%              Number of atoms          : 1158 (9615 expanded)
%              Number of equality atoms :  276 (1457 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f47,f46,f45,f44,f43,f42,f41])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f40])).

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
    inference(equality_resolution,[],[f67])).

fof(f79,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
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
    inference(equality_resolution,[],[f58])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_818,plain,
    ( ~ v1_tsep_1(X0_53,X1_53)
    | v1_tsep_1(X2_53,X1_53)
    | X2_53 != X0_53 ),
    theory(equality)).

cnf(c_1857,plain,
    ( ~ v1_tsep_1(X0_53,sK3)
    | v1_tsep_1(X1_53,sK3)
    | X1_53 != X0_53 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_4194,plain,
    ( v1_tsep_1(X0_53,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | X0_53 != sK3 ),
    inference(instantiation,[status(thm)],[c_1857])).

cnf(c_6059,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_4194])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_799,plain,
    ( m1_pre_topc(X0_53,X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1371,plain,
    ( m1_pre_topc(X0_53,X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_788,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1380,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_804,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1366,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_2230,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_1366])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2494,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2230,c_40])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_394,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_777,plain,
    ( ~ l1_pre_topc(X0_53)
    | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_1391,plain,
    ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_2967,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2494,c_1391])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_223,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_3])).

cnf(c_224,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_778,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_224])).

cnf(c_1390,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53))) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_5634,plain,
    ( m1_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2967,c_1390])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_792,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3819,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2967,c_792])).

cnf(c_5685,plain,
    ( m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(X0_53,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5634,c_3819])).

cnf(c_5706,plain,
    ( m1_pre_topc(X0_53,sK3) = iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5685,c_40,c_2230])).

cnf(c_5707,plain,
    ( m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(X0_53,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5706])).

cnf(c_5715,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_5707])).

cnf(c_5751,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5715])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_796,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1374,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_21,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_795,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1436,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1374,c_795])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
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

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_505,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_506,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_510,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_27])).

cnf(c_511,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_tsep_1(X0,X3)
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
    inference(renaming,[status(thm)],[c_510])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_554,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_tsep_1(X0,X3)
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
    inference(forward_subsumption_resolution,[status(thm)],[c_511,c_16])).

cnf(c_774,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),X0_54)
    | r1_tmap_1(X3_53,X1_53,sK4,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | ~ v1_tsep_1(X0_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X3_53) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_554])).

cnf(c_1394,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(X1_53) != u1_struct_0(sK3)
    | r1_tmap_1(X2_53,X0_53,k3_tmap_1(X3_53,X0_53,X1_53,X2_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(X1_53,X0_53,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X2_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
    | v1_tsep_1(X2_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | m1_pre_topc(X1_53,X3_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_2630,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v1_tsep_1(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1394])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2733,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | v1_tsep_1(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,X0_54) = iProver_top
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),X0_54) != iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2630,c_41,c_42,c_43])).

cnf(c_2734,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK3)
    | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(X0_53,sK1,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v1_tsep_1(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2733])).

cnf(c_2751,plain,
    ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_tsep_1(X0_53,sK3) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2734])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2828,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | v1_tsep_1(X0_53,sK3) != iProver_top
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2751,c_46,c_50])).

cnf(c_2829,plain,
    ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(X0_53,sK3) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2828])).

cnf(c_2845,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_2829])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_38,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_54,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_794,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1375,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_1417,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1375,c_795])).

cnf(c_3498,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2845,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1417])).

cnf(c_3499,plain,
    ( v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3498])).

cnf(c_3500,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3499])).

cnf(c_813,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_pre_topc(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_1901,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X2_53),u1_pre_topc(X2_53)),X3_53)
    | X3_53 != X1_53
    | g1_pre_topc(u1_struct_0(X2_53),u1_pre_topc(X2_53)) != X0_53 ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_2166,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0_53)
    | ~ m1_pre_topc(sK3,X1_53)
    | X0_53 != X1_53
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_2271,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0_53)
    | ~ m1_pre_topc(sK3,sK3)
    | X0_53 != sK3
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_3332,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_8,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_801,plain,
    ( v1_tsep_1(X0_53,X1_53)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),X1_53)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1847,plain,
    ( v1_tsep_1(X0_53,sK3)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),sK3)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)))
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_3290,plain,
    ( ~ v1_tsep_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_6,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_14,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_203,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_409,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X1 != X2
    | u1_struct_0(X0) != k2_struct_0(X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_203])).

cnf(c_410,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_776,plain,
    ( v1_tsep_1(X0_53,X1_53)
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | u1_struct_0(X0_53) != k2_struct_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_410])).

cnf(c_1848,plain,
    ( v1_tsep_1(X0_53,sK3)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_53) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_3073,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_812,plain,
    ( ~ v2_pre_topc(X0_53)
    | v2_pre_topc(X1_53)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_2354,plain,
    ( ~ v2_pre_topc(X0_53)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_53 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_3032,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2354])).

cnf(c_807,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2461,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_2272,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_2240,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2230])).

cnf(c_790,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1378,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_2229,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1378,c_1366])).

cnf(c_2239,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2229])).

cnf(c_814,plain,
    ( ~ l1_pre_topc(X0_53)
    | l1_pre_topc(X1_53)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_1746,plain,
    ( ~ l1_pre_topc(X0_53)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53)))
    | g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53)) != X0_53 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1867,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_1836,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_1838,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1836])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_805,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1365,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_1772,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_1365])).

cnf(c_1773,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1772])).

cnf(c_1768,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1378,c_1365])).

cnf(c_1769,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1768])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6059,c_5751,c_3500,c_3332,c_3290,c_3073,c_3032,c_2461,c_2272,c_2240,c_2239,c_2229,c_1867,c_1838,c_1773,c_1769,c_792,c_40,c_35,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:02:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.03/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/1.00  
% 3.03/1.00  ------  iProver source info
% 3.03/1.00  
% 3.03/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.03/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/1.00  git: non_committed_changes: false
% 3.03/1.00  git: last_make_outside_of_git: false
% 3.03/1.00  
% 3.03/1.00  ------ 
% 3.03/1.00  
% 3.03/1.00  ------ Input Options
% 3.03/1.00  
% 3.03/1.00  --out_options                           all
% 3.03/1.00  --tptp_safe_out                         true
% 3.03/1.00  --problem_path                          ""
% 3.03/1.00  --include_path                          ""
% 3.03/1.00  --clausifier                            res/vclausify_rel
% 3.03/1.00  --clausifier_options                    --mode clausify
% 3.03/1.00  --stdin                                 false
% 3.03/1.00  --stats_out                             all
% 3.03/1.00  
% 3.03/1.00  ------ General Options
% 3.03/1.00  
% 3.03/1.00  --fof                                   false
% 3.03/1.00  --time_out_real                         305.
% 3.03/1.00  --time_out_virtual                      -1.
% 3.03/1.00  --symbol_type_check                     false
% 3.03/1.00  --clausify_out                          false
% 3.03/1.00  --sig_cnt_out                           false
% 3.03/1.00  --trig_cnt_out                          false
% 3.03/1.00  --trig_cnt_out_tolerance                1.
% 3.03/1.00  --trig_cnt_out_sk_spl                   false
% 3.03/1.00  --abstr_cl_out                          false
% 3.03/1.00  
% 3.03/1.00  ------ Global Options
% 3.03/1.00  
% 3.03/1.00  --schedule                              default
% 3.03/1.00  --add_important_lit                     false
% 3.03/1.00  --prop_solver_per_cl                    1000
% 3.03/1.00  --min_unsat_core                        false
% 3.03/1.00  --soft_assumptions                      false
% 3.03/1.00  --soft_lemma_size                       3
% 3.03/1.00  --prop_impl_unit_size                   0
% 3.03/1.00  --prop_impl_unit                        []
% 3.03/1.00  --share_sel_clauses                     true
% 3.03/1.00  --reset_solvers                         false
% 3.03/1.00  --bc_imp_inh                            [conj_cone]
% 3.03/1.00  --conj_cone_tolerance                   3.
% 3.03/1.00  --extra_neg_conj                        none
% 3.03/1.00  --large_theory_mode                     true
% 3.03/1.00  --prolific_symb_bound                   200
% 3.03/1.00  --lt_threshold                          2000
% 3.03/1.00  --clause_weak_htbl                      true
% 3.03/1.00  --gc_record_bc_elim                     false
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing Options
% 3.03/1.00  
% 3.03/1.00  --preprocessing_flag                    true
% 3.03/1.00  --time_out_prep_mult                    0.1
% 3.03/1.00  --splitting_mode                        input
% 3.03/1.00  --splitting_grd                         true
% 3.03/1.00  --splitting_cvd                         false
% 3.03/1.00  --splitting_cvd_svl                     false
% 3.03/1.00  --splitting_nvd                         32
% 3.03/1.00  --sub_typing                            true
% 3.03/1.00  --prep_gs_sim                           true
% 3.03/1.00  --prep_unflatten                        true
% 3.03/1.00  --prep_res_sim                          true
% 3.03/1.00  --prep_upred                            true
% 3.03/1.00  --prep_sem_filter                       exhaustive
% 3.03/1.00  --prep_sem_filter_out                   false
% 3.03/1.00  --pred_elim                             true
% 3.03/1.00  --res_sim_input                         true
% 3.03/1.00  --eq_ax_congr_red                       true
% 3.03/1.00  --pure_diseq_elim                       true
% 3.03/1.00  --brand_transform                       false
% 3.03/1.00  --non_eq_to_eq                          false
% 3.03/1.00  --prep_def_merge                        true
% 3.03/1.00  --prep_def_merge_prop_impl              false
% 3.03/1.00  --prep_def_merge_mbd                    true
% 3.03/1.00  --prep_def_merge_tr_red                 false
% 3.03/1.00  --prep_def_merge_tr_cl                  false
% 3.03/1.00  --smt_preprocessing                     true
% 3.03/1.00  --smt_ac_axioms                         fast
% 3.03/1.00  --preprocessed_out                      false
% 3.03/1.00  --preprocessed_stats                    false
% 3.03/1.00  
% 3.03/1.00  ------ Abstraction refinement Options
% 3.03/1.00  
% 3.03/1.00  --abstr_ref                             []
% 3.03/1.00  --abstr_ref_prep                        false
% 3.03/1.00  --abstr_ref_until_sat                   false
% 3.03/1.00  --abstr_ref_sig_restrict                funpre
% 3.03/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.00  --abstr_ref_under                       []
% 3.03/1.00  
% 3.03/1.00  ------ SAT Options
% 3.03/1.00  
% 3.03/1.00  --sat_mode                              false
% 3.03/1.00  --sat_fm_restart_options                ""
% 3.03/1.00  --sat_gr_def                            false
% 3.03/1.00  --sat_epr_types                         true
% 3.03/1.00  --sat_non_cyclic_types                  false
% 3.03/1.00  --sat_finite_models                     false
% 3.03/1.00  --sat_fm_lemmas                         false
% 3.03/1.00  --sat_fm_prep                           false
% 3.03/1.00  --sat_fm_uc_incr                        true
% 3.03/1.00  --sat_out_model                         small
% 3.03/1.00  --sat_out_clauses                       false
% 3.03/1.00  
% 3.03/1.00  ------ QBF Options
% 3.03/1.00  
% 3.03/1.00  --qbf_mode                              false
% 3.03/1.00  --qbf_elim_univ                         false
% 3.03/1.00  --qbf_dom_inst                          none
% 3.03/1.00  --qbf_dom_pre_inst                      false
% 3.03/1.00  --qbf_sk_in                             false
% 3.03/1.00  --qbf_pred_elim                         true
% 3.03/1.00  --qbf_split                             512
% 3.03/1.00  
% 3.03/1.00  ------ BMC1 Options
% 3.03/1.00  
% 3.03/1.00  --bmc1_incremental                      false
% 3.03/1.00  --bmc1_axioms                           reachable_all
% 3.03/1.00  --bmc1_min_bound                        0
% 3.03/1.00  --bmc1_max_bound                        -1
% 3.03/1.00  --bmc1_max_bound_default                -1
% 3.03/1.00  --bmc1_symbol_reachability              true
% 3.03/1.00  --bmc1_property_lemmas                  false
% 3.03/1.00  --bmc1_k_induction                      false
% 3.03/1.00  --bmc1_non_equiv_states                 false
% 3.03/1.00  --bmc1_deadlock                         false
% 3.03/1.00  --bmc1_ucm                              false
% 3.03/1.00  --bmc1_add_unsat_core                   none
% 3.03/1.00  --bmc1_unsat_core_children              false
% 3.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.00  --bmc1_out_stat                         full
% 3.03/1.00  --bmc1_ground_init                      false
% 3.03/1.00  --bmc1_pre_inst_next_state              false
% 3.03/1.00  --bmc1_pre_inst_state                   false
% 3.03/1.00  --bmc1_pre_inst_reach_state             false
% 3.03/1.00  --bmc1_out_unsat_core                   false
% 3.03/1.00  --bmc1_aig_witness_out                  false
% 3.03/1.00  --bmc1_verbose                          false
% 3.03/1.00  --bmc1_dump_clauses_tptp                false
% 3.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.00  --bmc1_dump_file                        -
% 3.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.00  --bmc1_ucm_extend_mode                  1
% 3.03/1.00  --bmc1_ucm_init_mode                    2
% 3.03/1.00  --bmc1_ucm_cone_mode                    none
% 3.03/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.00  --bmc1_ucm_relax_model                  4
% 3.03/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.00  --bmc1_ucm_layered_model                none
% 3.03/1.00  --bmc1_ucm_max_lemma_size               10
% 3.03/1.00  
% 3.03/1.00  ------ AIG Options
% 3.03/1.00  
% 3.03/1.00  --aig_mode                              false
% 3.03/1.00  
% 3.03/1.00  ------ Instantiation Options
% 3.03/1.00  
% 3.03/1.00  --instantiation_flag                    true
% 3.03/1.00  --inst_sos_flag                         false
% 3.03/1.00  --inst_sos_phase                        true
% 3.03/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel_side                     num_symb
% 3.03/1.00  --inst_solver_per_active                1400
% 3.03/1.00  --inst_solver_calls_frac                1.
% 3.03/1.00  --inst_passive_queue_type               priority_queues
% 3.03/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.00  --inst_passive_queues_freq              [25;2]
% 3.03/1.00  --inst_dismatching                      true
% 3.03/1.00  --inst_eager_unprocessed_to_passive     true
% 3.03/1.00  --inst_prop_sim_given                   true
% 3.03/1.00  --inst_prop_sim_new                     false
% 3.03/1.00  --inst_subs_new                         false
% 3.03/1.00  --inst_eq_res_simp                      false
% 3.03/1.00  --inst_subs_given                       false
% 3.03/1.00  --inst_orphan_elimination               true
% 3.03/1.00  --inst_learning_loop_flag               true
% 3.03/1.00  --inst_learning_start                   3000
% 3.03/1.00  --inst_learning_factor                  2
% 3.03/1.00  --inst_start_prop_sim_after_learn       3
% 3.03/1.00  --inst_sel_renew                        solver
% 3.03/1.00  --inst_lit_activity_flag                true
% 3.03/1.00  --inst_restr_to_given                   false
% 3.03/1.00  --inst_activity_threshold               500
% 3.03/1.00  --inst_out_proof                        true
% 3.03/1.00  
% 3.03/1.00  ------ Resolution Options
% 3.03/1.00  
% 3.03/1.00  --resolution_flag                       true
% 3.03/1.00  --res_lit_sel                           adaptive
% 3.03/1.00  --res_lit_sel_side                      none
% 3.03/1.00  --res_ordering                          kbo
% 3.03/1.00  --res_to_prop_solver                    active
% 3.03/1.00  --res_prop_simpl_new                    false
% 3.03/1.00  --res_prop_simpl_given                  true
% 3.03/1.00  --res_passive_queue_type                priority_queues
% 3.03/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.00  --res_passive_queues_freq               [15;5]
% 3.03/1.00  --res_forward_subs                      full
% 3.03/1.00  --res_backward_subs                     full
% 3.03/1.00  --res_forward_subs_resolution           true
% 3.03/1.00  --res_backward_subs_resolution          true
% 3.03/1.00  --res_orphan_elimination                true
% 3.03/1.00  --res_time_limit                        2.
% 3.03/1.00  --res_out_proof                         true
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Options
% 3.03/1.00  
% 3.03/1.00  --superposition_flag                    true
% 3.03/1.00  --sup_passive_queue_type                priority_queues
% 3.03/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.00  --demod_completeness_check              fast
% 3.03/1.00  --demod_use_ground                      true
% 3.03/1.00  --sup_to_prop_solver                    passive
% 3.03/1.00  --sup_prop_simpl_new                    true
% 3.03/1.00  --sup_prop_simpl_given                  true
% 3.03/1.00  --sup_fun_splitting                     false
% 3.03/1.00  --sup_smt_interval                      50000
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Simplification Setup
% 3.03/1.00  
% 3.03/1.00  --sup_indices_passive                   []
% 3.03/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_full_bw                           [BwDemod]
% 3.03/1.00  --sup_immed_triv                        [TrivRules]
% 3.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_immed_bw_main                     []
% 3.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  
% 3.03/1.00  ------ Combination Options
% 3.03/1.00  
% 3.03/1.00  --comb_res_mult                         3
% 3.03/1.00  --comb_sup_mult                         2
% 3.03/1.00  --comb_inst_mult                        10
% 3.03/1.00  
% 3.03/1.00  ------ Debug Options
% 3.03/1.00  
% 3.03/1.00  --dbg_backtrace                         false
% 3.03/1.00  --dbg_dump_prop_clauses                 false
% 3.03/1.00  --dbg_dump_prop_clauses_file            -
% 3.03/1.00  --dbg_out_stat                          false
% 3.03/1.00  ------ Parsing...
% 3.03/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/1.00  ------ Proving...
% 3.03/1.00  ------ Problem Properties 
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  clauses                                 32
% 3.03/1.00  conjectures                             17
% 3.03/1.00  EPR                                     16
% 3.03/1.00  Horn                                    30
% 3.03/1.00  unary                                   17
% 3.03/1.00  binary                                  2
% 3.03/1.00  lits                                    116
% 3.03/1.00  lits eq                                 8
% 3.03/1.00  fd_pure                                 0
% 3.03/1.00  fd_pseudo                               0
% 3.03/1.00  fd_cond                                 0
% 3.03/1.00  fd_pseudo_cond                          0
% 3.03/1.00  AC symbols                              0
% 3.03/1.00  
% 3.03/1.00  ------ Schedule dynamic 5 is on 
% 3.03/1.00  
% 3.03/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  ------ 
% 3.03/1.00  Current options:
% 3.03/1.00  ------ 
% 3.03/1.00  
% 3.03/1.00  ------ Input Options
% 3.03/1.00  
% 3.03/1.00  --out_options                           all
% 3.03/1.00  --tptp_safe_out                         true
% 3.03/1.00  --problem_path                          ""
% 3.03/1.00  --include_path                          ""
% 3.03/1.00  --clausifier                            res/vclausify_rel
% 3.03/1.00  --clausifier_options                    --mode clausify
% 3.03/1.00  --stdin                                 false
% 3.03/1.00  --stats_out                             all
% 3.03/1.00  
% 3.03/1.00  ------ General Options
% 3.03/1.00  
% 3.03/1.00  --fof                                   false
% 3.03/1.00  --time_out_real                         305.
% 3.03/1.00  --time_out_virtual                      -1.
% 3.03/1.00  --symbol_type_check                     false
% 3.03/1.00  --clausify_out                          false
% 3.03/1.00  --sig_cnt_out                           false
% 3.03/1.00  --trig_cnt_out                          false
% 3.03/1.00  --trig_cnt_out_tolerance                1.
% 3.03/1.00  --trig_cnt_out_sk_spl                   false
% 3.03/1.00  --abstr_cl_out                          false
% 3.03/1.00  
% 3.03/1.00  ------ Global Options
% 3.03/1.00  
% 3.03/1.00  --schedule                              default
% 3.03/1.00  --add_important_lit                     false
% 3.03/1.00  --prop_solver_per_cl                    1000
% 3.03/1.00  --min_unsat_core                        false
% 3.03/1.00  --soft_assumptions                      false
% 3.03/1.00  --soft_lemma_size                       3
% 3.03/1.00  --prop_impl_unit_size                   0
% 3.03/1.00  --prop_impl_unit                        []
% 3.03/1.00  --share_sel_clauses                     true
% 3.03/1.00  --reset_solvers                         false
% 3.03/1.00  --bc_imp_inh                            [conj_cone]
% 3.03/1.00  --conj_cone_tolerance                   3.
% 3.03/1.00  --extra_neg_conj                        none
% 3.03/1.00  --large_theory_mode                     true
% 3.03/1.00  --prolific_symb_bound                   200
% 3.03/1.00  --lt_threshold                          2000
% 3.03/1.00  --clause_weak_htbl                      true
% 3.03/1.00  --gc_record_bc_elim                     false
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing Options
% 3.03/1.00  
% 3.03/1.00  --preprocessing_flag                    true
% 3.03/1.00  --time_out_prep_mult                    0.1
% 3.03/1.00  --splitting_mode                        input
% 3.03/1.00  --splitting_grd                         true
% 3.03/1.00  --splitting_cvd                         false
% 3.03/1.00  --splitting_cvd_svl                     false
% 3.03/1.00  --splitting_nvd                         32
% 3.03/1.00  --sub_typing                            true
% 3.03/1.00  --prep_gs_sim                           true
% 3.03/1.00  --prep_unflatten                        true
% 3.03/1.00  --prep_res_sim                          true
% 3.03/1.00  --prep_upred                            true
% 3.03/1.00  --prep_sem_filter                       exhaustive
% 3.03/1.00  --prep_sem_filter_out                   false
% 3.03/1.00  --pred_elim                             true
% 3.03/1.00  --res_sim_input                         true
% 3.03/1.00  --eq_ax_congr_red                       true
% 3.03/1.00  --pure_diseq_elim                       true
% 3.03/1.00  --brand_transform                       false
% 3.03/1.00  --non_eq_to_eq                          false
% 3.03/1.00  --prep_def_merge                        true
% 3.03/1.00  --prep_def_merge_prop_impl              false
% 3.03/1.00  --prep_def_merge_mbd                    true
% 3.03/1.00  --prep_def_merge_tr_red                 false
% 3.03/1.00  --prep_def_merge_tr_cl                  false
% 3.03/1.00  --smt_preprocessing                     true
% 3.03/1.00  --smt_ac_axioms                         fast
% 3.03/1.00  --preprocessed_out                      false
% 3.03/1.00  --preprocessed_stats                    false
% 3.03/1.00  
% 3.03/1.00  ------ Abstraction refinement Options
% 3.03/1.00  
% 3.03/1.00  --abstr_ref                             []
% 3.03/1.00  --abstr_ref_prep                        false
% 3.03/1.00  --abstr_ref_until_sat                   false
% 3.03/1.00  --abstr_ref_sig_restrict                funpre
% 3.03/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.00  --abstr_ref_under                       []
% 3.03/1.00  
% 3.03/1.00  ------ SAT Options
% 3.03/1.00  
% 3.03/1.00  --sat_mode                              false
% 3.03/1.00  --sat_fm_restart_options                ""
% 3.03/1.00  --sat_gr_def                            false
% 3.03/1.00  --sat_epr_types                         true
% 3.03/1.00  --sat_non_cyclic_types                  false
% 3.03/1.00  --sat_finite_models                     false
% 3.03/1.00  --sat_fm_lemmas                         false
% 3.03/1.00  --sat_fm_prep                           false
% 3.03/1.00  --sat_fm_uc_incr                        true
% 3.03/1.00  --sat_out_model                         small
% 3.03/1.00  --sat_out_clauses                       false
% 3.03/1.00  
% 3.03/1.00  ------ QBF Options
% 3.03/1.00  
% 3.03/1.00  --qbf_mode                              false
% 3.03/1.00  --qbf_elim_univ                         false
% 3.03/1.00  --qbf_dom_inst                          none
% 3.03/1.00  --qbf_dom_pre_inst                      false
% 3.03/1.00  --qbf_sk_in                             false
% 3.03/1.00  --qbf_pred_elim                         true
% 3.03/1.00  --qbf_split                             512
% 3.03/1.00  
% 3.03/1.00  ------ BMC1 Options
% 3.03/1.00  
% 3.03/1.00  --bmc1_incremental                      false
% 3.03/1.00  --bmc1_axioms                           reachable_all
% 3.03/1.00  --bmc1_min_bound                        0
% 3.03/1.00  --bmc1_max_bound                        -1
% 3.03/1.00  --bmc1_max_bound_default                -1
% 3.03/1.00  --bmc1_symbol_reachability              true
% 3.03/1.00  --bmc1_property_lemmas                  false
% 3.03/1.00  --bmc1_k_induction                      false
% 3.03/1.00  --bmc1_non_equiv_states                 false
% 3.03/1.00  --bmc1_deadlock                         false
% 3.03/1.00  --bmc1_ucm                              false
% 3.03/1.00  --bmc1_add_unsat_core                   none
% 3.03/1.00  --bmc1_unsat_core_children              false
% 3.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.00  --bmc1_out_stat                         full
% 3.03/1.00  --bmc1_ground_init                      false
% 3.03/1.00  --bmc1_pre_inst_next_state              false
% 3.03/1.00  --bmc1_pre_inst_state                   false
% 3.03/1.00  --bmc1_pre_inst_reach_state             false
% 3.03/1.00  --bmc1_out_unsat_core                   false
% 3.03/1.00  --bmc1_aig_witness_out                  false
% 3.03/1.00  --bmc1_verbose                          false
% 3.03/1.00  --bmc1_dump_clauses_tptp                false
% 3.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.00  --bmc1_dump_file                        -
% 3.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.00  --bmc1_ucm_extend_mode                  1
% 3.03/1.00  --bmc1_ucm_init_mode                    2
% 3.03/1.00  --bmc1_ucm_cone_mode                    none
% 3.03/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.00  --bmc1_ucm_relax_model                  4
% 3.03/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.00  --bmc1_ucm_layered_model                none
% 3.03/1.00  --bmc1_ucm_max_lemma_size               10
% 3.03/1.00  
% 3.03/1.00  ------ AIG Options
% 3.03/1.00  
% 3.03/1.00  --aig_mode                              false
% 3.03/1.00  
% 3.03/1.00  ------ Instantiation Options
% 3.03/1.00  
% 3.03/1.00  --instantiation_flag                    true
% 3.03/1.00  --inst_sos_flag                         false
% 3.03/1.00  --inst_sos_phase                        true
% 3.03/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.00  --inst_lit_sel_side                     none
% 3.03/1.00  --inst_solver_per_active                1400
% 3.03/1.00  --inst_solver_calls_frac                1.
% 3.03/1.00  --inst_passive_queue_type               priority_queues
% 3.03/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.00  --inst_passive_queues_freq              [25;2]
% 3.03/1.00  --inst_dismatching                      true
% 3.03/1.00  --inst_eager_unprocessed_to_passive     true
% 3.03/1.00  --inst_prop_sim_given                   true
% 3.03/1.00  --inst_prop_sim_new                     false
% 3.03/1.00  --inst_subs_new                         false
% 3.03/1.00  --inst_eq_res_simp                      false
% 3.03/1.00  --inst_subs_given                       false
% 3.03/1.00  --inst_orphan_elimination               true
% 3.03/1.00  --inst_learning_loop_flag               true
% 3.03/1.00  --inst_learning_start                   3000
% 3.03/1.00  --inst_learning_factor                  2
% 3.03/1.00  --inst_start_prop_sim_after_learn       3
% 3.03/1.00  --inst_sel_renew                        solver
% 3.03/1.00  --inst_lit_activity_flag                true
% 3.03/1.00  --inst_restr_to_given                   false
% 3.03/1.00  --inst_activity_threshold               500
% 3.03/1.00  --inst_out_proof                        true
% 3.03/1.00  
% 3.03/1.00  ------ Resolution Options
% 3.03/1.00  
% 3.03/1.00  --resolution_flag                       false
% 3.03/1.00  --res_lit_sel                           adaptive
% 3.03/1.00  --res_lit_sel_side                      none
% 3.03/1.00  --res_ordering                          kbo
% 3.03/1.00  --res_to_prop_solver                    active
% 3.03/1.00  --res_prop_simpl_new                    false
% 3.03/1.00  --res_prop_simpl_given                  true
% 3.03/1.00  --res_passive_queue_type                priority_queues
% 3.03/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.00  --res_passive_queues_freq               [15;5]
% 3.03/1.00  --res_forward_subs                      full
% 3.03/1.00  --res_backward_subs                     full
% 3.03/1.00  --res_forward_subs_resolution           true
% 3.03/1.00  --res_backward_subs_resolution          true
% 3.03/1.00  --res_orphan_elimination                true
% 3.03/1.00  --res_time_limit                        2.
% 3.03/1.00  --res_out_proof                         true
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Options
% 3.03/1.00  
% 3.03/1.00  --superposition_flag                    true
% 3.03/1.00  --sup_passive_queue_type                priority_queues
% 3.03/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.00  --demod_completeness_check              fast
% 3.03/1.00  --demod_use_ground                      true
% 3.03/1.00  --sup_to_prop_solver                    passive
% 3.03/1.00  --sup_prop_simpl_new                    true
% 3.03/1.00  --sup_prop_simpl_given                  true
% 3.03/1.00  --sup_fun_splitting                     false
% 3.03/1.00  --sup_smt_interval                      50000
% 3.03/1.00  
% 3.03/1.00  ------ Superposition Simplification Setup
% 3.03/1.00  
% 3.03/1.00  --sup_indices_passive                   []
% 3.03/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_full_bw                           [BwDemod]
% 3.03/1.00  --sup_immed_triv                        [TrivRules]
% 3.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_immed_bw_main                     []
% 3.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.00  
% 3.03/1.00  ------ Combination Options
% 3.03/1.00  
% 3.03/1.00  --comb_res_mult                         3
% 3.03/1.00  --comb_sup_mult                         2
% 3.03/1.00  --comb_inst_mult                        10
% 3.03/1.00  
% 3.03/1.00  ------ Debug Options
% 3.03/1.00  
% 3.03/1.00  --dbg_backtrace                         false
% 3.03/1.00  --dbg_dump_prop_clauses                 false
% 3.03/1.00  --dbg_dump_prop_clauses_file            -
% 3.03/1.00  --dbg_out_stat                          false
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  ------ Proving...
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  % SZS status Theorem for theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  fof(f10,axiom,(
% 3.03/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f28,plain,(
% 3.03/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f10])).
% 3.03/1.00  
% 3.03/1.00  fof(f64,plain,(
% 3.03/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f28])).
% 3.03/1.00  
% 3.03/1.00  fof(f13,conjecture,(
% 3.03/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f14,negated_conjecture,(
% 3.03/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.03/1.00    inference(negated_conjecture,[],[f13])).
% 3.03/1.00  
% 3.03/1.00  fof(f33,plain,(
% 3.03/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f14])).
% 3.03/1.00  
% 3.03/1.00  fof(f34,plain,(
% 3.03/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.03/1.00    inference(flattening,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f47,plain,(
% 3.03/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f46,plain,(
% 3.03/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f45,plain,(
% 3.03/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f44,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f43,plain,(
% 3.03/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f42,plain,(
% 3.03/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f41,plain,(
% 3.03/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f48,plain,(
% 3.03/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f47,f46,f45,f44,f43,f42,f41])).
% 3.03/1.00  
% 3.03/1.00  fof(f75,plain,(
% 3.03/1.00    m1_pre_topc(sK2,sK0)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f4,axiom,(
% 3.03/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f19,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f4])).
% 3.03/1.00  
% 3.03/1.00  fof(f52,plain,(
% 3.03/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f19])).
% 3.03/1.00  
% 3.03/1.00  fof(f70,plain,(
% 3.03/1.00    l1_pre_topc(sK0)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f3,axiom,(
% 3.03/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f18,plain,(
% 3.03/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f3])).
% 3.03/1.00  
% 3.03/1.00  fof(f51,plain,(
% 3.03/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f18])).
% 3.03/1.00  
% 3.03/1.00  fof(f2,axiom,(
% 3.03/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f17,plain,(
% 3.03/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f2])).
% 3.03/1.00  
% 3.03/1.00  fof(f50,plain,(
% 3.03/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f17])).
% 3.03/1.00  
% 3.03/1.00  fof(f5,axiom,(
% 3.03/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f20,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f5])).
% 3.03/1.00  
% 3.03/1.00  fof(f35,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.03/1.00    inference(nnf_transformation,[],[f20])).
% 3.03/1.00  
% 3.03/1.00  fof(f53,plain,(
% 3.03/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f35])).
% 3.03/1.00  
% 3.03/1.00  fof(f81,plain,(
% 3.03/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f85,plain,(
% 3.03/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f84,plain,(
% 3.03/1.00    sK5 = sK6),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f12,axiom,(
% 3.03/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f31,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f12])).
% 3.03/1.00  
% 3.03/1.00  fof(f32,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/1.00    inference(flattening,[],[f31])).
% 3.03/1.00  
% 3.03/1.00  fof(f40,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.03/1.00    inference(nnf_transformation,[],[f32])).
% 3.03/1.00  
% 3.03/1.00  fof(f67,plain,(
% 3.03/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f40])).
% 3.03/1.00  
% 3.03/1.00  fof(f94,plain,(
% 3.03/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.03/1.00    inference(equality_resolution,[],[f67])).
% 3.03/1.00  
% 3.03/1.00  fof(f79,plain,(
% 3.03/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f78,plain,(
% 3.03/1.00    v1_funct_1(sK4)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f11,axiom,(
% 3.03/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f29,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f11])).
% 3.03/1.00  
% 3.03/1.00  fof(f30,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(flattening,[],[f29])).
% 3.03/1.00  
% 3.03/1.00  fof(f65,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f30])).
% 3.03/1.00  
% 3.03/1.00  fof(f71,plain,(
% 3.03/1.00    ~v2_struct_0(sK1)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f72,plain,(
% 3.03/1.00    v2_pre_topc(sK1)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f73,plain,(
% 3.03/1.00    l1_pre_topc(sK1)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f76,plain,(
% 3.03/1.00    ~v2_struct_0(sK3)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f80,plain,(
% 3.03/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f68,plain,(
% 3.03/1.00    ~v2_struct_0(sK0)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f69,plain,(
% 3.03/1.00    v2_pre_topc(sK0)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f74,plain,(
% 3.03/1.00    ~v2_struct_0(sK2)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f77,plain,(
% 3.03/1.00    m1_pre_topc(sK3,sK0)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f82,plain,(
% 3.03/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f86,plain,(
% 3.03/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f83,plain,(
% 3.03/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.03/1.00    inference(cnf_transformation,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f7,axiom,(
% 3.03/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f23,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f7])).
% 3.03/1.00  
% 3.03/1.00  fof(f24,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(flattening,[],[f23])).
% 3.03/1.00  
% 3.03/1.00  fof(f36,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(nnf_transformation,[],[f24])).
% 3.03/1.00  
% 3.03/1.00  fof(f37,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(flattening,[],[f36])).
% 3.03/1.00  
% 3.03/1.00  fof(f58,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f37])).
% 3.03/1.00  
% 3.03/1.00  fof(f88,plain,(
% 3.03/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/1.00    inference(equality_resolution,[],[f58])).
% 3.03/1.00  
% 3.03/1.00  fof(f6,axiom,(
% 3.03/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f21,plain,(
% 3.03/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f6])).
% 3.03/1.00  
% 3.03/1.00  fof(f22,plain,(
% 3.03/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(flattening,[],[f21])).
% 3.03/1.00  
% 3.03/1.00  fof(f55,plain,(
% 3.03/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f22])).
% 3.03/1.00  
% 3.03/1.00  fof(f8,axiom,(
% 3.03/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f25,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f8])).
% 3.03/1.00  
% 3.03/1.00  fof(f26,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(flattening,[],[f25])).
% 3.03/1.00  
% 3.03/1.00  fof(f38,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(nnf_transformation,[],[f26])).
% 3.03/1.00  
% 3.03/1.00  fof(f39,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(flattening,[],[f38])).
% 3.03/1.00  
% 3.03/1.00  fof(f61,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f39])).
% 3.03/1.00  
% 3.03/1.00  fof(f92,plain,(
% 3.03/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/1.00    inference(equality_resolution,[],[f61])).
% 3.03/1.00  
% 3.03/1.00  fof(f9,axiom,(
% 3.03/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f27,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f9])).
% 3.03/1.00  
% 3.03/1.00  fof(f63,plain,(
% 3.03/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f27])).
% 3.03/1.00  
% 3.03/1.00  fof(f1,axiom,(
% 3.03/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f15,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f1])).
% 3.03/1.00  
% 3.03/1.00  fof(f16,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/1.00    inference(flattening,[],[f15])).
% 3.03/1.00  
% 3.03/1.00  fof(f49,plain,(
% 3.03/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f16])).
% 3.03/1.00  
% 3.03/1.00  cnf(c_818,plain,
% 3.03/1.00      ( ~ v1_tsep_1(X0_53,X1_53)
% 3.03/1.00      | v1_tsep_1(X2_53,X1_53)
% 3.03/1.00      | X2_53 != X0_53 ),
% 3.03/1.00      theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1857,plain,
% 3.03/1.00      ( ~ v1_tsep_1(X0_53,sK3) | v1_tsep_1(X1_53,sK3) | X1_53 != X0_53 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_818]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4194,plain,
% 3.03/1.00      ( v1_tsep_1(X0_53,sK3) | ~ v1_tsep_1(sK3,sK3) | X0_53 != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_1857]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6059,plain,
% 3.03/1.00      ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.03/1.00      | ~ v1_tsep_1(sK3,sK3)
% 3.03/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_4194]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_15,plain,
% 3.03/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_799,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,X0_53) | ~ l1_pre_topc(X0_53) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1371,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,X0_53) = iProver_top
% 3.03/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_30,negated_conjecture,
% 3.03/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_788,negated_conjecture,
% 3.03/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1380,plain,
% 3.03/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_804,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.03/1.00      | ~ l1_pre_topc(X1_53)
% 3.03/1.00      | l1_pre_topc(X0_53) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1366,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.03/1.00      | l1_pre_topc(X1_53) != iProver_top
% 3.03/1.00      | l1_pre_topc(X0_53) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2230,plain,
% 3.03/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.03/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1380,c_1366]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_35,negated_conjecture,
% 3.03/1.00      ( l1_pre_topc(sK0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_40,plain,
% 3.03/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2494,plain,
% 3.03/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_2230,c_40]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2,plain,
% 3.03/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1,plain,
% 3.03/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_394,plain,
% 3.03/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.03/1.00      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_777,plain,
% 3.03/1.00      ( ~ l1_pre_topc(X0_53) | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_394]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1391,plain,
% 3.03/1.00      ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
% 3.03/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2967,plain,
% 3.03/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_2494,c_1391]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.03/1.00      | ~ l1_pre_topc(X0)
% 3.03/1.00      | ~ l1_pre_topc(X1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_223,plain,
% 3.03/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.03/1.00      | ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ l1_pre_topc(X1) ),
% 3.03/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5,c_3]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_224,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.03/1.00      | ~ l1_pre_topc(X1) ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_223]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_778,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.03/1.00      | m1_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53)))
% 3.03/1.00      | ~ l1_pre_topc(X1_53) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_224]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1390,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53))) = iProver_top
% 3.03/1.00      | l1_pre_topc(X1_53) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5634,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,sK2) != iProver_top
% 3.03/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_2967,c_1390]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_24,negated_conjecture,
% 3.03/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.03/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_792,negated_conjecture,
% 3.03/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3819,plain,
% 3.03/1.00      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_2967,c_792]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5685,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,sK2) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,sK3) = iProver_top
% 3.03/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_5634,c_3819]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5706,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,sK3) = iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,sK2) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_5685,c_40,c_2230]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5707,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,sK2) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,sK3) = iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_5706]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5715,plain,
% 3.03/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.03/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1371,c_5707]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5751,plain,
% 3.03/1.00      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 3.03/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5715]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_20,negated_conjecture,
% 3.03/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.03/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_796,negated_conjecture,
% 3.03/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1374,plain,
% 3.03/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_21,negated_conjecture,
% 3.03/1.00      ( sK5 = sK6 ),
% 3.03/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_795,negated_conjecture,
% 3.03/1.00      ( sK5 = sK6 ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1436,plain,
% 3.03/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1374,c_795]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_17,plain,
% 3.03/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.03/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.03/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.03/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.03/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.03/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.03/1.00      | ~ v1_tsep_1(X4,X0)
% 3.03/1.00      | ~ m1_pre_topc(X4,X0)
% 3.03/1.00      | ~ m1_pre_topc(X0,X5)
% 3.03/1.00      | ~ m1_pre_topc(X4,X5)
% 3.03/1.00      | v2_struct_0(X5)
% 3.03/1.00      | v2_struct_0(X1)
% 3.03/1.00      | v2_struct_0(X4)
% 3.03/1.00      | v2_struct_0(X0)
% 3.03/1.00      | ~ v1_funct_1(X2)
% 3.03/1.00      | ~ l1_pre_topc(X5)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X5)
% 3.03/1.00      | ~ v2_pre_topc(X1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_26,negated_conjecture,
% 3.03/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_505,plain,
% 3.03/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.03/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.03/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.03/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.03/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.03/1.00      | ~ v1_tsep_1(X4,X0)
% 3.03/1.00      | ~ m1_pre_topc(X4,X0)
% 3.03/1.00      | ~ m1_pre_topc(X0,X5)
% 3.03/1.00      | ~ m1_pre_topc(X4,X5)
% 3.03/1.00      | v2_struct_0(X1)
% 3.03/1.00      | v2_struct_0(X0)
% 3.03/1.00      | v2_struct_0(X5)
% 3.03/1.00      | v2_struct_0(X4)
% 3.03/1.00      | ~ v1_funct_1(X2)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ l1_pre_topc(X5)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X5)
% 3.03/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.03/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.03/1.00      | sK4 != X2 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_506,plain,
% 3.03/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.03/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.03/1.00      | ~ v1_tsep_1(X0,X3)
% 3.03/1.00      | ~ m1_pre_topc(X0,X3)
% 3.03/1.00      | ~ m1_pre_topc(X3,X2)
% 3.03/1.00      | ~ m1_pre_topc(X0,X2)
% 3.03/1.00      | v2_struct_0(X1)
% 3.03/1.00      | v2_struct_0(X3)
% 3.03/1.00      | v2_struct_0(X2)
% 3.03/1.00      | v2_struct_0(X0)
% 3.03/1.00      | ~ v1_funct_1(sK4)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ l1_pre_topc(X2)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X2)
% 3.03/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.03/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_505]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_27,negated_conjecture,
% 3.03/1.00      ( v1_funct_1(sK4) ),
% 3.03/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_510,plain,
% 3.03/1.00      ( v2_struct_0(X0)
% 3.03/1.00      | v2_struct_0(X2)
% 3.03/1.00      | v2_struct_0(X3)
% 3.03/1.00      | v2_struct_0(X1)
% 3.03/1.00      | ~ m1_pre_topc(X0,X2)
% 3.03/1.00      | ~ m1_pre_topc(X3,X2)
% 3.03/1.00      | ~ m1_pre_topc(X0,X3)
% 3.03/1.00      | ~ v1_tsep_1(X0,X3)
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.03/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.03/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ l1_pre_topc(X2)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X2)
% 3.03/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.03/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_506,c_27]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_511,plain,
% 3.03/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.03/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.03/1.00      | ~ v1_tsep_1(X0,X3)
% 3.03/1.00      | ~ m1_pre_topc(X0,X2)
% 3.03/1.00      | ~ m1_pre_topc(X0,X3)
% 3.03/1.00      | ~ m1_pre_topc(X3,X2)
% 3.03/1.00      | v2_struct_0(X1)
% 3.03/1.00      | v2_struct_0(X0)
% 3.03/1.00      | v2_struct_0(X2)
% 3.03/1.00      | v2_struct_0(X3)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ l1_pre_topc(X2)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X2)
% 3.03/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.03/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_510]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_16,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ m1_pre_topc(X2,X0)
% 3.03/1.00      | m1_pre_topc(X2,X1)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_554,plain,
% 3.03/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.03/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.03/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.03/1.00      | ~ v1_tsep_1(X0,X3)
% 3.03/1.00      | ~ m1_pre_topc(X0,X3)
% 3.03/1.00      | ~ m1_pre_topc(X3,X2)
% 3.03/1.00      | v2_struct_0(X1)
% 3.03/1.00      | v2_struct_0(X0)
% 3.03/1.00      | v2_struct_0(X2)
% 3.03/1.00      | v2_struct_0(X3)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ l1_pre_topc(X2)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X2)
% 3.03/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.03/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.03/1.00      inference(forward_subsumption_resolution,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_511,c_16]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_774,plain,
% 3.03/1.00      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),X0_54)
% 3.03/1.00      | r1_tmap_1(X3_53,X1_53,sK4,X0_54)
% 3.03/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 3.03/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
% 3.03/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 3.03/1.00      | ~ v1_tsep_1(X0_53,X3_53)
% 3.03/1.00      | ~ m1_pre_topc(X0_53,X3_53)
% 3.03/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 3.03/1.00      | v2_struct_0(X1_53)
% 3.03/1.00      | v2_struct_0(X0_53)
% 3.03/1.00      | v2_struct_0(X2_53)
% 3.03/1.00      | v2_struct_0(X3_53)
% 3.03/1.00      | ~ l1_pre_topc(X1_53)
% 3.03/1.00      | ~ l1_pre_topc(X2_53)
% 3.03/1.00      | ~ v2_pre_topc(X1_53)
% 3.03/1.00      | ~ v2_pre_topc(X2_53)
% 3.03/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 3.03/1.00      | u1_struct_0(X3_53) != u1_struct_0(sK3) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_554]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1394,plain,
% 3.03/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 3.03/1.00      | u1_struct_0(X1_53) != u1_struct_0(sK3)
% 3.03/1.00      | r1_tmap_1(X2_53,X0_53,k3_tmap_1(X3_53,X0_53,X1_53,X2_53,sK4),X0_54) != iProver_top
% 3.03/1.00      | r1_tmap_1(X1_53,X0_53,sK4,X0_54) = iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X2_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
% 3.03/1.00      | v1_tsep_1(X2_53,X1_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X1_53,X3_53) != iProver_top
% 3.03/1.00      | v2_struct_0(X0_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X2_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X3_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X1_53) = iProver_top
% 3.03/1.00      | l1_pre_topc(X0_53) != iProver_top
% 3.03/1.00      | l1_pre_topc(X3_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X0_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X3_53) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2630,plain,
% 3.03/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 3.03/1.00      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),X0_54) != iProver_top
% 3.03/1.00      | r1_tmap_1(X0_53,sK1,sK4,X0_54) = iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_tsep_1(X1_53,X0_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 3.03/1.00      | v2_struct_0(X1_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X0_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X2_53) = iProver_top
% 3.03/1.00      | v2_struct_0(sK1) = iProver_top
% 3.03/1.00      | l1_pre_topc(X2_53) != iProver_top
% 3.03/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.03/1.00      | v2_pre_topc(X2_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 3.03/1.00      inference(equality_resolution,[status(thm)],[c_1394]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_34,negated_conjecture,
% 3.03/1.00      ( ~ v2_struct_0(sK1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_41,plain,
% 3.03/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_33,negated_conjecture,
% 3.03/1.00      ( v2_pre_topc(sK1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_42,plain,
% 3.03/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_32,negated_conjecture,
% 3.03/1.00      ( l1_pre_topc(sK1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_43,plain,
% 3.03/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2733,plain,
% 3.03/1.00      ( v2_pre_topc(X2_53) != iProver_top
% 3.03/1.00      | v2_struct_0(X2_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X0_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X1_53) = iProver_top
% 3.03/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 3.03/1.00      | v1_tsep_1(X1_53,X0_53) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.03/1.00      | r1_tmap_1(X0_53,sK1,sK4,X0_54) = iProver_top
% 3.03/1.00      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),X0_54) != iProver_top
% 3.03/1.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 3.03/1.00      | l1_pre_topc(X2_53) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_2630,c_41,c_42,c_43]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2734,plain,
% 3.03/1.00      ( u1_struct_0(X0_53) != u1_struct_0(sK3)
% 3.03/1.00      | r1_tmap_1(X1_53,sK1,k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4),X0_54) != iProver_top
% 3.03/1.00      | r1_tmap_1(X0_53,sK1,sK4,X0_54) = iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_tsep_1(X1_53,X0_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 3.03/1.00      | v2_struct_0(X1_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X0_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X2_53) = iProver_top
% 3.03/1.00      | l1_pre_topc(X2_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X2_53) != iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_2733]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2751,plain,
% 3.03/1.00      ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
% 3.03/1.00      | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_tsep_1(X0_53,sK3) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 3.03/1.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 3.03/1.00      | v2_struct_0(X1_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X0_53) = iProver_top
% 3.03/1.00      | v2_struct_0(sK3) = iProver_top
% 3.03/1.00      | l1_pre_topc(X1_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 3.03/1.00      inference(equality_resolution,[status(thm)],[c_2734]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_29,negated_conjecture,
% 3.03/1.00      ( ~ v2_struct_0(sK3) ),
% 3.03/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_46,plain,
% 3.03/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_25,negated_conjecture,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.03/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_50,plain,
% 3.03/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2828,plain,
% 3.03/1.00      ( v2_struct_0(X0_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X1_53) = iProver_top
% 3.03/1.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 3.03/1.00      | v1_tsep_1(X0_53,sK3) != iProver_top
% 3.03/1.00      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
% 3.03/1.00      | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 3.03/1.00      | l1_pre_topc(X1_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_2751,c_46,c_50]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2829,plain,
% 3.03/1.00      ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
% 3.03/1.00      | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 3.03/1.00      | v1_tsep_1(X0_53,sK3) != iProver_top
% 3.03/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 3.03/1.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 3.03/1.00      | v2_struct_0(X1_53) = iProver_top
% 3.03/1.00      | v2_struct_0(X0_53) = iProver_top
% 3.03/1.00      | l1_pre_topc(X1_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X1_53) != iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_2828]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2845,plain,
% 3.03/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.03/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.03/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.03/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.03/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.03/1.00      | v2_struct_0(sK0) = iProver_top
% 3.03/1.00      | v2_struct_0(sK2) = iProver_top
% 3.03/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.03/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1436,c_2829]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_37,negated_conjecture,
% 3.03/1.00      ( ~ v2_struct_0(sK0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_38,plain,
% 3.03/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_36,negated_conjecture,
% 3.03/1.00      ( v2_pre_topc(sK0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_39,plain,
% 3.03/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_31,negated_conjecture,
% 3.03/1.00      ( ~ v2_struct_0(sK2) ),
% 3.03/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_44,plain,
% 3.03/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_28,negated_conjecture,
% 3.03/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_47,plain,
% 3.03/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_23,negated_conjecture,
% 3.03/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_51,plain,
% 3.03/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_19,negated_conjecture,
% 3.03/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.03/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_54,plain,
% 3.03/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_22,negated_conjecture,
% 3.03/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_794,negated_conjecture,
% 3.03/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1375,plain,
% 3.03/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1417,plain,
% 3.03/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1375,c_795]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3498,plain,
% 3.03/1.00      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.03/1.00      | v1_tsep_1(sK2,sK3) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_2845,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1417]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3499,plain,
% 3.03/1.00      ( v1_tsep_1(sK2,sK3) != iProver_top
% 3.03/1.00      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_3498]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3500,plain,
% 3.03/1.00      ( ~ v1_tsep_1(sK2,sK3) | ~ m1_pre_topc(sK2,sK3) ),
% 3.03/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3499]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_813,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.03/1.00      | m1_pre_topc(X2_53,X3_53)
% 3.03/1.00      | X2_53 != X0_53
% 3.03/1.00      | X3_53 != X1_53 ),
% 3.03/1.00      theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1901,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.03/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X2_53),u1_pre_topc(X2_53)),X3_53)
% 3.03/1.00      | X3_53 != X1_53
% 3.03/1.00      | g1_pre_topc(u1_struct_0(X2_53),u1_pre_topc(X2_53)) != X0_53 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_813]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2166,plain,
% 3.03/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0_53)
% 3.03/1.00      | ~ m1_pre_topc(sK3,X1_53)
% 3.03/1.00      | X0_53 != X1_53
% 3.03/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_1901]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2271,plain,
% 3.03/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0_53)
% 3.03/1.00      | ~ m1_pre_topc(sK3,sK3)
% 3.03/1.00      | X0_53 != sK3
% 3.03/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_2166]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3332,plain,
% 3.03/1.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.03/1.00      | ~ m1_pre_topc(sK3,sK3)
% 3.03/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 3.03/1.00      | sK3 != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_2271]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_8,plain,
% 3.03/1.00      ( v1_tsep_1(X0,X1)
% 3.03/1.00      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.03/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ l1_pre_topc(X0)
% 3.03/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X0)
% 3.03/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.03/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_801,plain,
% 3.03/1.00      ( v1_tsep_1(X0_53,X1_53)
% 3.03/1.00      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),X1_53)
% 3.03/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),X1_53)
% 3.03/1.00      | ~ l1_pre_topc(X1_53)
% 3.03/1.00      | ~ l1_pre_topc(X0_53)
% 3.03/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)))
% 3.03/1.00      | ~ v2_pre_topc(X1_53)
% 3.03/1.00      | ~ v2_pre_topc(X0_53)
% 3.03/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53))) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1847,plain,
% 3.03/1.00      ( v1_tsep_1(X0_53,sK3)
% 3.03/1.00      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),sK3)
% 3.03/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)),sK3)
% 3.03/1.00      | ~ l1_pre_topc(X0_53)
% 3.03/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)))
% 3.03/1.00      | ~ l1_pre_topc(sK3)
% 3.03/1.00      | ~ v2_pre_topc(X0_53)
% 3.03/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_53),u1_pre_topc(X0_53)))
% 3.03/1.00      | ~ v2_pre_topc(sK3) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_801]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3290,plain,
% 3.03/1.00      ( ~ v1_tsep_1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.03/1.00      | v1_tsep_1(sK2,sK3)
% 3.03/1.00      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.03/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.03/1.00      | ~ l1_pre_topc(sK2)
% 3.03/1.00      | ~ l1_pre_topc(sK3)
% 3.03/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.03/1.00      | ~ v2_pre_topc(sK2)
% 3.03/1.00      | ~ v2_pre_topc(sK3) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_1847]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6,plain,
% 3.03/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.03/1.00      | ~ l1_pre_topc(X0)
% 3.03/1.00      | ~ v2_pre_topc(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_12,plain,
% 3.03/1.00      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/1.00      | v1_tsep_1(X0,X1)
% 3.03/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.03/1.00      | ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_14,plain,
% 3.03/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/1.00      | ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ l1_pre_topc(X1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_203,plain,
% 3.03/1.00      ( v1_tsep_1(X0,X1)
% 3.03/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.03/1.00      | ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X1) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_12,c_14]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_409,plain,
% 3.03/1.00      ( v1_tsep_1(X0,X1)
% 3.03/1.00      | ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ l1_pre_topc(X2)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X2)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | X1 != X2
% 3.03/1.00      | u1_struct_0(X0) != k2_struct_0(X2) ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_203]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_410,plain,
% 3.03/1.00      ( v1_tsep_1(X0,X1)
% 3.03/1.00      | ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_776,plain,
% 3.03/1.00      ( v1_tsep_1(X0_53,X1_53)
% 3.03/1.00      | ~ m1_pre_topc(X0_53,X1_53)
% 3.03/1.00      | ~ l1_pre_topc(X1_53)
% 3.03/1.00      | ~ v2_pre_topc(X1_53)
% 3.03/1.00      | u1_struct_0(X0_53) != k2_struct_0(X1_53) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_410]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1848,plain,
% 3.03/1.00      ( v1_tsep_1(X0_53,sK3)
% 3.03/1.00      | ~ m1_pre_topc(X0_53,sK3)
% 3.03/1.00      | ~ l1_pre_topc(sK3)
% 3.03/1.00      | ~ v2_pre_topc(sK3)
% 3.03/1.00      | u1_struct_0(X0_53) != k2_struct_0(sK3) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_776]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3073,plain,
% 3.03/1.00      ( v1_tsep_1(sK3,sK3)
% 3.03/1.00      | ~ m1_pre_topc(sK3,sK3)
% 3.03/1.00      | ~ l1_pre_topc(sK3)
% 3.03/1.00      | ~ v2_pre_topc(sK3)
% 3.03/1.00      | u1_struct_0(sK3) != k2_struct_0(sK3) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_1848]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_812,plain,
% 3.03/1.00      ( ~ v2_pre_topc(X0_53) | v2_pre_topc(X1_53) | X1_53 != X0_53 ),
% 3.03/1.00      theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2354,plain,
% 3.03/1.00      ( ~ v2_pre_topc(X0_53)
% 3.03/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.03/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_53 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_812]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3032,plain,
% 3.03/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.03/1.00      | ~ v2_pre_topc(sK3)
% 3.03/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_2354]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_807,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2461,plain,
% 3.03/1.00      ( sK3 = sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_807]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2272,plain,
% 3.03/1.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_799]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2240,plain,
% 3.03/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.03/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2230]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_790,negated_conjecture,
% 3.03/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1378,plain,
% 3.03/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2229,plain,
% 3.03/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.03/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1378,c_1366]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2239,plain,
% 3.03/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.03/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2229]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_814,plain,
% 3.03/1.00      ( ~ l1_pre_topc(X0_53) | l1_pre_topc(X1_53) | X1_53 != X0_53 ),
% 3.03/1.00      theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1746,plain,
% 3.03/1.00      ( ~ l1_pre_topc(X0_53)
% 3.03/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53)))
% 3.03/1.00      | g1_pre_topc(u1_struct_0(X1_53),u1_pre_topc(X1_53)) != X0_53 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_814]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1867,plain,
% 3.03/1.00      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.03/1.00      | ~ l1_pre_topc(sK3)
% 3.03/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_1746]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1836,plain,
% 3.03/1.00      ( ~ l1_pre_topc(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_777]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1838,plain,
% 3.03/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3)
% 3.03/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1836]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_0,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.03/1.00      | ~ l1_pre_topc(X1)
% 3.03/1.00      | ~ v2_pre_topc(X1)
% 3.03/1.00      | v2_pre_topc(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_805,plain,
% 3.03/1.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.03/1.00      | ~ l1_pre_topc(X1_53)
% 3.03/1.00      | ~ v2_pre_topc(X1_53)
% 3.03/1.00      | v2_pre_topc(X0_53) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1365,plain,
% 3.03/1.00      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.03/1.00      | l1_pre_topc(X1_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X1_53) != iProver_top
% 3.03/1.00      | v2_pre_topc(X0_53) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1772,plain,
% 3.03/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.03/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.03/1.00      | v2_pre_topc(sK2) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1380,c_1365]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1773,plain,
% 3.03/1.00      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK2) ),
% 3.03/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1772]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1768,plain,
% 3.03/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.03/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.03/1.00      | v2_pre_topc(sK3) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1378,c_1365]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1769,plain,
% 3.03/1.00      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 3.03/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1768]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(contradiction,plain,
% 3.03/1.00      ( $false ),
% 3.03/1.00      inference(minisat,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_6059,c_5751,c_3500,c_3332,c_3290,c_3073,c_3032,c_2461,
% 3.03/1.00                 c_2272,c_2240,c_2239,c_2229,c_1867,c_1838,c_1773,c_1769,
% 3.03/1.00                 c_792,c_40,c_35,c_36]) ).
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  ------                               Statistics
% 3.03/1.00  
% 3.03/1.00  ------ General
% 3.03/1.00  
% 3.03/1.00  abstr_ref_over_cycles:                  0
% 3.03/1.00  abstr_ref_under_cycles:                 0
% 3.03/1.00  gc_basic_clause_elim:                   0
% 3.03/1.00  forced_gc_time:                         0
% 3.03/1.00  parsing_time:                           0.011
% 3.03/1.00  unif_index_cands_time:                  0.
% 3.03/1.00  unif_index_add_time:                    0.
% 3.03/1.00  orderings_time:                         0.
% 3.03/1.00  out_proof_time:                         0.014
% 3.03/1.00  total_time:                             0.257
% 3.03/1.00  num_of_symbols:                         59
% 3.03/1.00  num_of_terms:                           3828
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing
% 3.03/1.00  
% 3.03/1.00  num_of_splits:                          0
% 3.03/1.00  num_of_split_atoms:                     0
% 3.03/1.00  num_of_reused_defs:                     0
% 3.03/1.00  num_eq_ax_congr_red:                    8
% 3.03/1.00  num_of_sem_filtered_clauses:            1
% 3.03/1.00  num_of_subtypes:                        3
% 3.03/1.00  monotx_restored_types:                  0
% 3.03/1.00  sat_num_of_epr_types:                   0
% 3.03/1.00  sat_num_of_non_cyclic_types:            0
% 3.03/1.00  sat_guarded_non_collapsed_types:        0
% 3.03/1.00  num_pure_diseq_elim:                    0
% 3.03/1.00  simp_replaced_by:                       0
% 3.03/1.00  res_preprocessed:                       170
% 3.03/1.00  prep_upred:                             0
% 3.03/1.00  prep_unflattend:                        3
% 3.03/1.00  smt_new_axioms:                         0
% 3.03/1.00  pred_elim_cands:                        7
% 3.03/1.00  pred_elim:                              4
% 3.03/1.00  pred_elim_cl:                           5
% 3.03/1.00  pred_elim_cycles:                       6
% 3.03/1.00  merged_defs:                            0
% 3.03/1.00  merged_defs_ncl:                        0
% 3.03/1.00  bin_hyper_res:                          0
% 3.03/1.00  prep_cycles:                            4
% 3.03/1.00  pred_elim_time:                         0.008
% 3.03/1.00  splitting_time:                         0.
% 3.03/1.00  sem_filter_time:                        0.
% 3.03/1.00  monotx_time:                            0.
% 3.03/1.00  subtype_inf_time:                       0.
% 3.03/1.00  
% 3.03/1.00  ------ Problem properties
% 3.03/1.00  
% 3.03/1.00  clauses:                                32
% 3.03/1.00  conjectures:                            17
% 3.03/1.00  epr:                                    16
% 3.03/1.00  horn:                                   30
% 3.03/1.00  ground:                                 17
% 3.03/1.00  unary:                                  17
% 3.03/1.00  binary:                                 2
% 3.03/1.00  lits:                                   116
% 3.03/1.00  lits_eq:                                8
% 3.03/1.00  fd_pure:                                0
% 3.03/1.00  fd_pseudo:                              0
% 3.03/1.00  fd_cond:                                0
% 3.03/1.00  fd_pseudo_cond:                         0
% 3.03/1.00  ac_symbols:                             0
% 3.03/1.00  
% 3.03/1.00  ------ Propositional Solver
% 3.03/1.00  
% 3.03/1.00  prop_solver_calls:                      28
% 3.03/1.00  prop_fast_solver_calls:                 1659
% 3.03/1.00  smt_solver_calls:                       0
% 3.03/1.00  smt_fast_solver_calls:                  0
% 3.03/1.00  prop_num_of_clauses:                    1708
% 3.03/1.00  prop_preprocess_simplified:             5733
% 3.03/1.00  prop_fo_subsumed:                       55
% 3.03/1.00  prop_solver_time:                       0.
% 3.03/1.00  smt_solver_time:                        0.
% 3.03/1.00  smt_fast_solver_time:                   0.
% 3.03/1.00  prop_fast_solver_time:                  0.
% 3.03/1.00  prop_unsat_core_time:                   0.
% 3.03/1.00  
% 3.03/1.00  ------ QBF
% 3.03/1.00  
% 3.03/1.00  qbf_q_res:                              0
% 3.03/1.00  qbf_num_tautologies:                    0
% 3.03/1.00  qbf_prep_cycles:                        0
% 3.03/1.00  
% 3.03/1.00  ------ BMC1
% 3.03/1.00  
% 3.03/1.00  bmc1_current_bound:                     -1
% 3.03/1.00  bmc1_last_solved_bound:                 -1
% 3.03/1.00  bmc1_unsat_core_size:                   -1
% 3.03/1.00  bmc1_unsat_core_parents_size:           -1
% 3.03/1.00  bmc1_merge_next_fun:                    0
% 3.03/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.03/1.00  
% 3.03/1.00  ------ Instantiation
% 3.03/1.00  
% 3.03/1.00  inst_num_of_clauses:                    498
% 3.03/1.00  inst_num_in_passive:                    63
% 3.03/1.00  inst_num_in_active:                     353
% 3.03/1.00  inst_num_in_unprocessed:                81
% 3.03/1.00  inst_num_of_loops:                      383
% 3.03/1.00  inst_num_of_learning_restarts:          0
% 3.03/1.00  inst_num_moves_active_passive:          23
% 3.03/1.00  inst_lit_activity:                      0
% 3.03/1.00  inst_lit_activity_moves:                0
% 3.03/1.00  inst_num_tautologies:                   0
% 3.03/1.00  inst_num_prop_implied:                  0
% 3.03/1.00  inst_num_existing_simplified:           0
% 3.03/1.00  inst_num_eq_res_simplified:             0
% 3.03/1.00  inst_num_child_elim:                    0
% 3.03/1.00  inst_num_of_dismatching_blockings:      339
% 3.03/1.00  inst_num_of_non_proper_insts:           774
% 3.03/1.00  inst_num_of_duplicates:                 0
% 3.03/1.00  inst_inst_num_from_inst_to_res:         0
% 3.03/1.00  inst_dismatching_checking_time:         0.
% 3.03/1.00  
% 3.03/1.00  ------ Resolution
% 3.03/1.00  
% 3.03/1.00  res_num_of_clauses:                     0
% 3.03/1.00  res_num_in_passive:                     0
% 3.03/1.00  res_num_in_active:                      0
% 3.03/1.00  res_num_of_loops:                       174
% 3.03/1.00  res_forward_subset_subsumed:            103
% 3.03/1.00  res_backward_subset_subsumed:           6
% 3.03/1.00  res_forward_subsumed:                   0
% 3.03/1.00  res_backward_subsumed:                  0
% 3.03/1.00  res_forward_subsumption_resolution:     2
% 3.03/1.00  res_backward_subsumption_resolution:    0
% 3.03/1.00  res_clause_to_clause_subsumption:       528
% 3.03/1.00  res_orphan_elimination:                 0
% 3.03/1.00  res_tautology_del:                      139
% 3.03/1.00  res_num_eq_res_simplified:              0
% 3.03/1.00  res_num_sel_changes:                    0
% 3.03/1.00  res_moves_from_active_to_pass:          0
% 3.03/1.00  
% 3.03/1.00  ------ Superposition
% 3.03/1.00  
% 3.03/1.00  sup_time_total:                         0.
% 3.03/1.00  sup_time_generating:                    0.
% 3.03/1.00  sup_time_sim_full:                      0.
% 3.03/1.00  sup_time_sim_immed:                     0.
% 3.03/1.00  
% 3.03/1.00  sup_num_of_clauses:                     117
% 3.03/1.00  sup_num_in_active:                      64
% 3.03/1.00  sup_num_in_passive:                     53
% 3.03/1.00  sup_num_of_loops:                       76
% 3.03/1.00  sup_fw_superposition:                   80
% 3.03/1.00  sup_bw_superposition:                   50
% 3.03/1.00  sup_immediate_simplified:               35
% 3.03/1.00  sup_given_eliminated:                   0
% 3.03/1.00  comparisons_done:                       0
% 3.03/1.00  comparisons_avoided:                    0
% 3.03/1.00  
% 3.03/1.00  ------ Simplifications
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  sim_fw_subset_subsumed:                 14
% 3.03/1.00  sim_bw_subset_subsumed:                 12
% 3.03/1.00  sim_fw_subsumed:                        4
% 3.03/1.00  sim_bw_subsumed:                        0
% 3.03/1.00  sim_fw_subsumption_res:                 4
% 3.03/1.00  sim_bw_subsumption_res:                 0
% 3.03/1.00  sim_tautology_del:                      13
% 3.03/1.00  sim_eq_tautology_del:                   0
% 3.03/1.00  sim_eq_res_simp:                        0
% 3.03/1.00  sim_fw_demodulated:                     0
% 3.03/1.00  sim_bw_demodulated:                     11
% 3.03/1.00  sim_light_normalised:                   23
% 3.03/1.00  sim_joinable_taut:                      0
% 3.03/1.00  sim_joinable_simp:                      0
% 3.03/1.00  sim_ac_normalised:                      0
% 3.03/1.00  sim_smt_subsumption:                    0
% 3.03/1.00  
%------------------------------------------------------------------------------
