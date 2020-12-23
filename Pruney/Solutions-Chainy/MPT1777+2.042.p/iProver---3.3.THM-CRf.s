%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:33 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  190 (1101 expanded)
%              Number of clauses        :  111 ( 252 expanded)
%              Number of leaves         :   22 ( 476 expanded)
%              Depth                    :   19
%              Number of atoms          :  872 (14424 expanded)
%              Number of equality atoms :  187 (2081 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f36,f50,f49,f48,f47,f46,f45,f44])).

fof(f80,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f34])).

fof(f72,plain,(
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

fof(f97,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f90,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17582,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17597,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19303,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17582,c_17597])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7226,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_8,c_32])).

cnf(c_7227,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7226])).

cnf(c_19750,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19303,c_42,c_7227])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17598,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19755,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_19750,c_17598])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17599,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20100,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_19755,c_17599])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_17583,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19302,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_17583,c_17597])).

cnf(c_7224,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_8,c_30])).

cnf(c_7225,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7224])).

cnf(c_19623,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19302,c_42,c_7225])).

cnf(c_19628,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19623,c_17598])).

cnf(c_19992,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_19628,c_17599])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17594,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20482,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19992,c_17594])).

cnf(c_23950,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20482,c_42,c_7225])).

cnf(c_23951,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_23950])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17600,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_23962,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23951,c_17600])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17603,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23997,plain,
    ( u1_struct_0(X0) = k2_struct_0(sK3)
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23962,c_17603])).

cnf(c_26996,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20100,c_23997])).

cnf(c_27011,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK2)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26996,c_20100])).

cnf(c_20625,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_20100,c_17594])).

cnf(c_24953,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20625,c_42,c_7227])).

cnf(c_24954,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_24953])).

cnf(c_24965,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24954,c_17600])).

cnf(c_25185,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19992,c_24965])).

cnf(c_652,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_18433,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_18498,plain,
    ( X0 = u1_struct_0(X1)
    | X0 != k2_struct_0(X1)
    | u1_struct_0(X1) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_18433])).

cnf(c_18731,plain,
    ( u1_struct_0(X0) != k2_struct_0(X0)
    | k2_struct_0(sK3) = u1_struct_0(X0)
    | k2_struct_0(sK3) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_18498])).

cnf(c_22198,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK3) = u1_struct_0(sK2)
    | k2_struct_0(sK3) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_18731])).

cnf(c_18500,plain,
    ( X0 != X1
    | u1_struct_0(X2) != X1
    | u1_struct_0(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_18548,plain,
    ( X0 != u1_struct_0(X1)
    | u1_struct_0(X1) = X0
    | u1_struct_0(X1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_18500])).

cnf(c_18549,plain,
    ( X0 != u1_struct_0(X1)
    | u1_struct_0(X1) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_18548])).

cnf(c_18755,plain,
    ( u1_struct_0(X0) = k2_struct_0(sK3)
    | k2_struct_0(sK3) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_18549])).

cnf(c_21828,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3)
    | k2_struct_0(sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_18755])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_17593,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17596,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20253,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_17596])).

cnf(c_20444,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20253,c_42,c_7227])).

cnf(c_20445,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_20444])).

cnf(c_20453,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_20445])).

cnf(c_661,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_17958,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | v3_pre_topc(u1_struct_0(X1),sK3)
    | u1_struct_0(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_18028,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | u1_struct_0(X0) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_17958])).

cnf(c_19932,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18028])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_361,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_362,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_17574,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_18463,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_17574])).

cnf(c_18783,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18463,c_42,c_7227])).

cnf(c_18784,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_18783])).

cnf(c_18791,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_18784])).

cnf(c_18792,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18791])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18402,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_379,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_380,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_379])).

cnf(c_17947,plain,
    ( v1_tsep_1(X0,sK3)
    | ~ v3_pre_topc(u1_struct_0(X0),sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_18188,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_17947])).

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
    inference(cnf_transformation,[],[f97])).

cnf(c_17890,plain,
    ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2)
    | r1_tmap_1(sK3,sK1,sK4,X2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(X0,sK3)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_18073,plain,
    ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(X0,sK3)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ m1_subset_1(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17890])).

cnf(c_18086,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18073])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_17589,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_17654,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17589,c_23])).

cnf(c_17771,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17654])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8455,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_30])).

cnf(c_7250,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7175,plain,
    ( ~ l1_struct_0(sK2)
    | u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6409,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6448,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6409,c_23])).

cnf(c_6686,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6448])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27011,c_25185,c_22198,c_21828,c_20453,c_19932,c_18792,c_18791,c_18402,c_18188,c_18086,c_17771,c_8455,c_7250,c_7227,c_7226,c_7225,c_7224,c_7175,c_6686,c_21,c_25,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_42,c_37,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 38
% 7.75/1.50  conjectures                             19
% 7.75/1.50  EPR                                     20
% 7.75/1.50  Horn                                    36
% 7.75/1.50  unary                                   20
% 7.75/1.50  binary                                  5
% 7.75/1.50  lits                                    109
% 7.75/1.50  lits eq                                 4
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 0
% 7.75/1.50  fd_pseudo_cond                          1
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Input Options Time Limit: Unbounded
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f15,conjecture,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f16,negated_conjecture,(
% 7.75/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.75/1.50    inference(negated_conjecture,[],[f15])).
% 7.75/1.50  
% 7.75/1.50  fof(f35,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f36,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f35])).
% 7.75/1.50  
% 7.75/1.50  fof(f50,plain,(
% 7.75/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f47,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f46,plain,(
% 7.75/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f51,plain,(
% 7.75/1.50    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f36,f50,f49,f48,f47,f46,f45,f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f80,plain,(
% 7.75/1.50    m1_pre_topc(sK2,sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f6,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f22,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f6])).
% 7.75/1.50  
% 7.75/1.50  fof(f60,plain,(
% 7.75/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f75,plain,(
% 7.75/1.50    l1_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f5,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f21,plain,(
% 7.75/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f5])).
% 7.75/1.50  
% 7.75/1.50  fof(f59,plain,(
% 7.75/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f21])).
% 7.75/1.50  
% 7.75/1.50  fof(f4,axiom,(
% 7.75/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f20,plain,(
% 7.75/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f4])).
% 7.75/1.50  
% 7.75/1.50  fof(f58,plain,(
% 7.75/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f20])).
% 7.75/1.50  
% 7.75/1.50  fof(f82,plain,(
% 7.75/1.50    m1_pre_topc(sK3,sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f29,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f68,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f29])).
% 7.75/1.50  
% 7.75/1.50  fof(f2,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.75/1.50    inference(nnf_transformation,[],[f2])).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f1,axiom,(
% 7.75/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f37,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(nnf_transformation,[],[f1])).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(flattening,[],[f37])).
% 7.75/1.50  
% 7.75/1.50  fof(f54,plain,(
% 7.75/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f12,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f30,plain,(
% 7.75/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f12])).
% 7.75/1.50  
% 7.75/1.50  fof(f69,plain,(
% 7.75/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f86,plain,(
% 7.75/1.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f7,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f7])).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f61,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f8,axiom,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f24,plain,(
% 7.75/1.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f8])).
% 7.75/1.50  
% 7.75/1.50  fof(f25,plain,(
% 7.75/1.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f24])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f10,axiom,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f27,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f10])).
% 7.75/1.50  
% 7.75/1.50  fof(f28,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f66,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f95,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.75/1.50    inference(equality_resolution,[],[f66])).
% 7.75/1.50  
% 7.75/1.50  fof(f14,axiom,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f33,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f14])).
% 7.75/1.50  
% 7.75/1.50  fof(f34,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f33])).
% 7.75/1.50  
% 7.75/1.50  fof(f43,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f34])).
% 7.75/1.50  
% 7.75/1.50  fof(f72,plain,(
% 7.75/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f43])).
% 7.75/1.50  
% 7.75/1.50  fof(f97,plain,(
% 7.75/1.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(equality_resolution,[],[f72])).
% 7.75/1.50  
% 7.75/1.50  fof(f90,plain,(
% 7.75/1.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f89,plain,(
% 7.75/1.50    sK5 = sK6),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f18,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f19,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f57,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f19])).
% 7.75/1.50  
% 7.75/1.50  fof(f88,plain,(
% 7.75/1.50    m1_subset_1(sK6,u1_struct_0(sK2))),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f91,plain,(
% 7.75/1.50    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f87,plain,(
% 7.75/1.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f85,plain,(
% 7.75/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f84,plain,(
% 7.75/1.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f83,plain,(
% 7.75/1.50    v1_funct_1(sK4)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f81,plain,(
% 7.75/1.50    ~v2_struct_0(sK3)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f79,plain,(
% 7.75/1.50    ~v2_struct_0(sK2)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f78,plain,(
% 7.75/1.50    l1_pre_topc(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f77,plain,(
% 7.75/1.50    v2_pre_topc(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f76,plain,(
% 7.75/1.50    ~v2_struct_0(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f74,plain,(
% 7.75/1.50    v2_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  fof(f73,plain,(
% 7.75/1.50    ~v2_struct_0(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f51])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_32,negated_conjecture,
% 7.75/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17582,plain,
% 7.75/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8,plain,
% 7.75/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17597,plain,
% 7.75/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.50      | l1_pre_topc(X1) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19303,plain,
% 7.75/1.50      ( l1_pre_topc(sK0) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK2) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_17582,c_17597]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_37,negated_conjecture,
% 7.75/1.50      ( l1_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_42,plain,
% 7.75/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7226,plain,
% 7.75/1.50      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_8,c_32]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7227,plain,
% 7.75/1.50      ( l1_pre_topc(sK0) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK2) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_7226]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19750,plain,
% 7.75/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_19303,c_42,c_7227]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7,plain,
% 7.75/1.50      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17598,plain,
% 7.75/1.50      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19755,plain,
% 7.75/1.50      ( l1_struct_0(sK2) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_19750,c_17598]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6,plain,
% 7.75/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17599,plain,
% 7.75/1.50      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.75/1.50      | l1_struct_0(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20100,plain,
% 7.75/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_19755,c_17599]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_30,negated_conjecture,
% 7.75/1.50      ( m1_pre_topc(sK3,sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17583,plain,
% 7.75/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19302,plain,
% 7.75/1.50      ( l1_pre_topc(sK0) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK3) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_17583,c_17597]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7224,plain,
% 7.75/1.50      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_8,c_30]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7225,plain,
% 7.75/1.50      ( l1_pre_topc(sK0) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK3) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_7224]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19623,plain,
% 7.75/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_19302,c_42,c_7225]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19628,plain,
% 7.75/1.50      ( l1_struct_0(sK3) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_19623,c_17598]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19992,plain,
% 7.75/1.50      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_19628,c_17599]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16,plain,
% 7.75/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17594,plain,
% 7.75/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.75/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20482,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.75/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.75/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_19992,c_17594]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23950,plain,
% 7.75/1.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_20482,c_42,c_7225]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23951,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.75/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_23950]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17600,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.75/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23962,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.75/1.50      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_23951,c_17600]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_0,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.75/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17603,plain,
% 7.75/1.50      ( X0 = X1
% 7.75/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23997,plain,
% 7.75/1.50      ( u1_struct_0(X0) = k2_struct_0(sK3)
% 7.75/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.75/1.50      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_23962,c_17603]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_26996,plain,
% 7.75/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK3)
% 7.75/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.75/1.50      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_20100,c_23997]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_27011,plain,
% 7.75/1.50      ( k2_struct_0(sK3) = k2_struct_0(sK2)
% 7.75/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.75/1.50      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_26996,c_20100]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20625,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.75/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 7.75/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_20100,c_17594]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24953,plain,
% 7.75/1.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_20625,c_42,c_7227]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24954,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.75/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_24953]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24965,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.75/1.50      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_24954,c_17600]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_25185,plain,
% 7.75/1.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 7.75/1.50      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_19992,c_24965]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_652,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18433,plain,
% 7.75/1.50      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_652]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18498,plain,
% 7.75/1.50      ( X0 = u1_struct_0(X1)
% 7.75/1.50      | X0 != k2_struct_0(X1)
% 7.75/1.50      | u1_struct_0(X1) != k2_struct_0(X1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18433]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18731,plain,
% 7.75/1.50      ( u1_struct_0(X0) != k2_struct_0(X0)
% 7.75/1.50      | k2_struct_0(sK3) = u1_struct_0(X0)
% 7.75/1.50      | k2_struct_0(sK3) != k2_struct_0(X0) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18498]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22198,plain,
% 7.75/1.50      ( u1_struct_0(sK2) != k2_struct_0(sK2)
% 7.75/1.50      | k2_struct_0(sK3) = u1_struct_0(sK2)
% 7.75/1.50      | k2_struct_0(sK3) != k2_struct_0(sK2) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18731]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18500,plain,
% 7.75/1.50      ( X0 != X1 | u1_struct_0(X2) != X1 | u1_struct_0(X2) = X0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_652]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18548,plain,
% 7.75/1.50      ( X0 != u1_struct_0(X1)
% 7.75/1.50      | u1_struct_0(X1) = X0
% 7.75/1.50      | u1_struct_0(X1) != u1_struct_0(X1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18500]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18549,plain,
% 7.75/1.50      ( X0 != u1_struct_0(X1) | u1_struct_0(X1) = X0 ),
% 7.75/1.50      inference(equality_resolution_simp,[status(thm)],[c_18548]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18755,plain,
% 7.75/1.50      ( u1_struct_0(X0) = k2_struct_0(sK3)
% 7.75/1.50      | k2_struct_0(sK3) != u1_struct_0(X0) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18549]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21828,plain,
% 7.75/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK3)
% 7.75/1.50      | k2_struct_0(sK3) != u1_struct_0(sK2) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18755]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17,plain,
% 7.75/1.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17593,plain,
% 7.75/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_26,negated_conjecture,
% 7.75/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.75/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9,plain,
% 7.75/1.50      ( m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X0)
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17596,plain,
% 7.75/1.50      ( m1_pre_topc(X0,X1) = iProver_top
% 7.75/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.75/1.50      | l1_pre_topc(X1) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20253,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top
% 7.75/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_26,c_17596]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20444,plain,
% 7.75/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_20253,c_42,c_7227]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20445,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.75/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_20444]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20453,plain,
% 7.75/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top
% 7.75/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_17593,c_20445]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_661,plain,
% 7.75/1.50      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 7.75/1.50      theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17958,plain,
% 7.75/1.50      ( ~ v3_pre_topc(X0,sK3)
% 7.75/1.50      | v3_pre_topc(u1_struct_0(X1),sK3)
% 7.75/1.50      | u1_struct_0(X1) != X0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_661]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18028,plain,
% 7.75/1.50      ( v3_pre_topc(u1_struct_0(X0),sK3)
% 7.75/1.50      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.75/1.50      | u1_struct_0(X0) != k2_struct_0(sK3) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_17958]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19932,plain,
% 7.75/1.50      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 7.75/1.50      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.75/1.50      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18028]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10,plain,
% 7.75/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X0)
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_361,plain,
% 7.75/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.75/1.50      | ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_10,c_8]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_362,plain,
% 7.75/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_361]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17574,plain,
% 7.75/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.75/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18463,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK3) = iProver_top
% 7.75/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_26,c_17574]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18783,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK3) = iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_18463,c_42,c_7227]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18784,plain,
% 7.75/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.75/1.50      | m1_pre_topc(X0,sK3) = iProver_top ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_18783]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18791,plain,
% 7.75/1.50      ( m1_pre_topc(sK2,sK3) = iProver_top
% 7.75/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_17593,c_18784]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18792,plain,
% 7.75/1.50      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 7.75/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_18791]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_11,plain,
% 7.75/1.50      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.75/1.50      | ~ l1_pre_topc(X0)
% 7.75/1.50      | ~ v2_pre_topc(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18402,plain,
% 7.75/1.50      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.75/1.50      | ~ l1_pre_topc(sK3)
% 7.75/1.50      | ~ v2_pre_topc(sK3) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14,plain,
% 7.75/1.50      ( v1_tsep_1(X0,X1)
% 7.75/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.75/1.50      | ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_379,plain,
% 7.75/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.75/1.50      | v1_tsep_1(X0,X1)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_14,c_16]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_380,plain,
% 7.75/1.50      ( v1_tsep_1(X0,X1)
% 7.75/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.75/1.50      | ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_379]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17947,plain,
% 7.75/1.50      ( v1_tsep_1(X0,sK3)
% 7.75/1.50      | ~ v3_pre_topc(u1_struct_0(X0),sK3)
% 7.75/1.50      | ~ m1_pre_topc(X0,sK3)
% 7.75/1.50      | ~ l1_pre_topc(sK3)
% 7.75/1.50      | ~ v2_pre_topc(sK3) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_380]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18188,plain,
% 7.75/1.50      ( v1_tsep_1(sK2,sK3)
% 7.75/1.50      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 7.75/1.50      | ~ m1_pre_topc(sK2,sK3)
% 7.75/1.50      | ~ l1_pre_topc(sK3)
% 7.75/1.50      | ~ v2_pre_topc(sK3) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_17947]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19,plain,
% 7.75/1.50      ( r1_tmap_1(X0,X1,X2,X3)
% 7.75/1.50      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.75/1.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.75/1.50      | ~ v1_tsep_1(X4,X0)
% 7.75/1.50      | ~ m1_pre_topc(X4,X5)
% 7.75/1.50      | ~ m1_pre_topc(X4,X0)
% 7.75/1.50      | ~ m1_pre_topc(X0,X5)
% 7.75/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.75/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.75/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.75/1.50      | v2_struct_0(X5)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | v2_struct_0(X4)
% 7.75/1.50      | v2_struct_0(X0)
% 7.75/1.50      | ~ v1_funct_1(X2)
% 7.75/1.50      | ~ l1_pre_topc(X5)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X5)
% 7.75/1.50      | ~ v2_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17890,plain,
% 7.75/1.50      ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2)
% 7.75/1.50      | r1_tmap_1(sK3,sK1,sK4,X2)
% 7.75/1.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.75/1.50      | ~ v1_tsep_1(X0,sK3)
% 7.75/1.50      | ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_pre_topc(X0,sK3)
% 7.75/1.50      | ~ m1_pre_topc(sK3,X1)
% 7.75/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.75/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 7.75/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.75/1.50      | v2_struct_0(X0)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | v2_struct_0(sK1)
% 7.75/1.50      | v2_struct_0(sK3)
% 7.75/1.50      | ~ v1_funct_1(sK4)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ l1_pre_topc(sK1)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(sK1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18073,plain,
% 7.75/1.50      ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
% 7.75/1.50      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 7.75/1.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.75/1.50      | ~ v1_tsep_1(X0,sK3)
% 7.75/1.50      | ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_pre_topc(X0,sK3)
% 7.75/1.50      | ~ m1_pre_topc(sK3,X1)
% 7.75/1.50      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 7.75/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 7.75/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.75/1.50      | v2_struct_0(X0)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | v2_struct_0(sK1)
% 7.75/1.50      | v2_struct_0(sK3)
% 7.75/1.50      | ~ v1_funct_1(sK4)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ l1_pre_topc(sK1)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(sK1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_17890]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18086,plain,
% 7.75/1.50      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 7.75/1.50      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 7.75/1.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.75/1.50      | ~ v1_tsep_1(sK2,sK3)
% 7.75/1.50      | ~ m1_pre_topc(sK2,sK0)
% 7.75/1.50      | ~ m1_pre_topc(sK2,sK3)
% 7.75/1.50      | ~ m1_pre_topc(sK3,sK0)
% 7.75/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.75/1.50      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 7.75/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.75/1.50      | v2_struct_0(sK0)
% 7.75/1.50      | v2_struct_0(sK2)
% 7.75/1.50      | v2_struct_0(sK1)
% 7.75/1.50      | v2_struct_0(sK3)
% 7.75/1.50      | ~ v1_funct_1(sK4)
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | ~ l1_pre_topc(sK1)
% 7.75/1.50      | ~ v2_pre_topc(sK0)
% 7.75/1.50      | ~ v2_pre_topc(sK1) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18073]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22,negated_conjecture,
% 7.75/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.75/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17589,plain,
% 7.75/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23,negated_conjecture,
% 7.75/1.50      ( sK5 = sK6 ),
% 7.75/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17654,plain,
% 7.75/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_17589,c_23]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17771,plain,
% 7.75/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 7.75/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_17654]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5,plain,
% 7.75/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | v2_pre_topc(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8455,plain,
% 7.75/1.50      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_5,c_30]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7250,plain,
% 7.75/1.50      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7175,plain,
% 7.75/1.50      ( ~ l1_struct_0(sK2) | u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6409,plain,
% 7.75/1.50      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6448,plain,
% 7.75/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_6409,c_23]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6686,plain,
% 7.75/1.50      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.75/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_6448]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21,negated_conjecture,
% 7.75/1.50      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 7.75/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_25,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_27,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.75/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_28,negated_conjecture,
% 7.75/1.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_29,negated_conjecture,
% 7.75/1.50      ( v1_funct_1(sK4) ),
% 7.75/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_31,negated_conjecture,
% 7.75/1.50      ( ~ v2_struct_0(sK3) ),
% 7.75/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_33,negated_conjecture,
% 7.75/1.50      ( ~ v2_struct_0(sK2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_34,negated_conjecture,
% 7.75/1.50      ( l1_pre_topc(sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_35,negated_conjecture,
% 7.75/1.50      ( v2_pre_topc(sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_36,negated_conjecture,
% 7.75/1.50      ( ~ v2_struct_0(sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_38,negated_conjecture,
% 7.75/1.50      ( v2_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_39,negated_conjecture,
% 7.75/1.50      ( ~ v2_struct_0(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(contradiction,plain,
% 7.75/1.50      ( $false ),
% 7.75/1.50      inference(minisat,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_27011,c_25185,c_22198,c_21828,c_20453,c_19932,c_18792,
% 7.75/1.50                 c_18791,c_18402,c_18188,c_18086,c_17771,c_8455,c_7250,
% 7.75/1.50                 c_7227,c_7226,c_7225,c_7224,c_7175,c_6686,c_21,c_25,
% 7.75/1.50                 c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_42,
% 7.75/1.50                 c_37,c_38,c_39]) ).
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  ------                               Statistics
% 7.75/1.50  
% 7.75/1.50  ------ Selected
% 7.75/1.50  
% 7.75/1.50  total_time:                             0.775
% 7.75/1.50  
%------------------------------------------------------------------------------
