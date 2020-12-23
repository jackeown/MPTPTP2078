%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:27 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  189 (1066 expanded)
%              Number of clauses        :  100 ( 214 expanded)
%              Number of leaves         :   23 ( 483 expanded)
%              Depth                    :   15
%              Number of atoms          :  934 (15085 expanded)
%              Number of equality atoms :  269 (2269 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f53,f52,f51,f50,f49,f48,f47])).

fof(f92,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f46])).

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
    inference(equality_resolution,[],[f74])).

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

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f55,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f58,plain,(
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

fof(f57,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1138,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1202,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1138,c_22])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1141,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1142,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1380,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1141,c_1142])).

cnf(c_6399,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1380])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1132,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1152,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2561,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1152])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1812,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

cnf(c_1813,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_2766,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2561,c_41,c_1813])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1156,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3142,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | v1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_1156])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1814,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_4,c_31])).

cnf(c_1815,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2809,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_31])).

cnf(c_2810,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2809])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1149,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3269,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1149])).

cnf(c_3514,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3142,c_40,c_41,c_1815,c_2810,c_3269])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1147,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4061,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1147])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2978,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2983,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2978])).

cnf(c_4063,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1147])).

cnf(c_4210,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(X0,X1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4061,c_41,c_1815,c_2983,c_4063])).

cnf(c_4211,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_4210])).

cnf(c_4216,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3514,c_4211])).

cnf(c_6417,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6399,c_4216])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1153,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2771,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_1153])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1154,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2906,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2771,c_1154])).

cnf(c_10,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1146,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3612,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2906,c_1146])).

cnf(c_2807,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_29])).

cnf(c_2808,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2807])).

cnf(c_5700,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3612,c_40,c_41,c_1813,c_2808])).

cnf(c_12,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_14,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_280,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_281,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_1122,plain,
    ( v1_tsep_1(X0,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_4340,plain,
    ( v1_tsep_1(sK2,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4216,c_1122])).

cnf(c_6159,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5700,c_4340])).

cnf(c_1130,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1143,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3738,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1143])).

cnf(c_3744,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3738,c_25])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4228,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3744,c_39,c_40,c_41,c_45])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1144,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4646,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_1144])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_55,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_50,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_49,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_48,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_46,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6417,c_6159,c_4646,c_2808,c_1813,c_55,c_52,c_51,c_50,c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.75/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/1.00  
% 3.75/1.00  ------  iProver source info
% 3.75/1.00  
% 3.75/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.75/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/1.00  git: non_committed_changes: false
% 3.75/1.00  git: last_make_outside_of_git: false
% 3.75/1.00  
% 3.75/1.00  ------ 
% 3.75/1.00  ------ Parsing...
% 3.75/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/1.00  ------ Proving...
% 3.75/1.00  ------ Problem Properties 
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  clauses                                 38
% 3.75/1.00  conjectures                             19
% 3.75/1.00  EPR                                     17
% 3.75/1.00  Horn                                    34
% 3.75/1.00  unary                                   19
% 3.75/1.00  binary                                  3
% 3.75/1.00  lits                                    120
% 3.75/1.00  lits eq                                 9
% 3.75/1.00  fd_pure                                 0
% 3.75/1.00  fd_pseudo                               0
% 3.75/1.00  fd_cond                                 0
% 3.75/1.00  fd_pseudo_cond                          2
% 3.75/1.00  AC symbols                              0
% 3.75/1.00  
% 3.75/1.00  ------ Input Options Time Limit: Unbounded
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  ------ 
% 3.75/1.00  Current options:
% 3.75/1.00  ------ 
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  ------ Proving...
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  % SZS status Theorem for theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  fof(f16,conjecture,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f17,negated_conjecture,(
% 3.75/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.75/1.00    inference(negated_conjecture,[],[f16])).
% 3.75/1.00  
% 3.75/1.00  fof(f42,plain,(
% 3.75/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f17])).
% 3.75/1.00  
% 3.75/1.00  fof(f43,plain,(
% 3.75/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.75/1.00    inference(flattening,[],[f42])).
% 3.75/1.00  
% 3.75/1.00  fof(f53,plain,(
% 3.75/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f52,plain,(
% 3.75/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f51,plain,(
% 3.75/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f50,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f49,plain,(
% 3.75/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f48,plain,(
% 3.75/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f47,plain,(
% 3.75/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f54,plain,(
% 3.75/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f53,f52,f51,f50,f49,f48,f47])).
% 3.75/1.00  
% 3.75/1.00  fof(f92,plain,(
% 3.75/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f91,plain,(
% 3.75/1.00    sK5 = sK6),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f15,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f40,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f15])).
% 3.75/1.00  
% 3.75/1.00  fof(f41,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.75/1.00    inference(flattening,[],[f40])).
% 3.75/1.00  
% 3.75/1.00  fof(f46,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.75/1.00    inference(nnf_transformation,[],[f41])).
% 3.75/1.00  
% 3.75/1.00  fof(f74,plain,(
% 3.75/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f46])).
% 3.75/1.00  
% 3.75/1.00  fof(f97,plain,(
% 3.75/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.75/1.00    inference(equality_resolution,[],[f74])).
% 3.75/1.00  
% 3.75/1.00  fof(f14,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f38,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f14])).
% 3.75/1.00  
% 3.75/1.00  fof(f39,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/1.00    inference(flattening,[],[f38])).
% 3.75/1.00  
% 3.75/1.00  fof(f72,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f39])).
% 3.75/1.00  
% 3.75/1.00  fof(f84,plain,(
% 3.75/1.00    m1_pre_topc(sK3,sK0)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f5,axiom,(
% 3.75/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f24,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.75/1.00    inference(ennf_transformation,[],[f5])).
% 3.75/1.00  
% 3.75/1.00  fof(f59,plain,(
% 3.75/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f24])).
% 3.75/1.00  
% 3.75/1.00  fof(f77,plain,(
% 3.75/1.00    l1_pre_topc(sK0)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f1,axiom,(
% 3.75/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f18,plain,(
% 3.75/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.75/1.00    inference(ennf_transformation,[],[f1])).
% 3.75/1.00  
% 3.75/1.00  fof(f19,plain,(
% 3.75/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.75/1.00    inference(flattening,[],[f18])).
% 3.75/1.00  
% 3.75/1.00  fof(f55,plain,(
% 3.75/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f19])).
% 3.75/1.00  
% 3.75/1.00  fof(f76,plain,(
% 3.75/1.00    v2_pre_topc(sK0)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f82,plain,(
% 3.75/1.00    m1_pre_topc(sK2,sK0)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f2,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f20,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f2])).
% 3.75/1.00  
% 3.75/1.00  fof(f21,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/1.00    inference(flattening,[],[f20])).
% 3.75/1.00  
% 3.75/1.00  fof(f56,plain,(
% 3.75/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f21])).
% 3.75/1.00  
% 3.75/1.00  fof(f88,plain,(
% 3.75/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f7,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f26,plain,(
% 3.75/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f7])).
% 3.75/1.00  
% 3.75/1.00  fof(f27,plain,(
% 3.75/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/1.00    inference(flattening,[],[f26])).
% 3.75/1.00  
% 3.75/1.00  fof(f61,plain,(
% 3.75/1.00    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f27])).
% 3.75/1.00  
% 3.75/1.00  fof(f8,axiom,(
% 3.75/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f28,plain,(
% 3.75/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.75/1.00    inference(ennf_transformation,[],[f8])).
% 3.75/1.00  
% 3.75/1.00  fof(f63,plain,(
% 3.75/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f28])).
% 3.75/1.00  
% 3.75/1.00  fof(f6,axiom,(
% 3.75/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f25,plain,(
% 3.75/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/1.00    inference(ennf_transformation,[],[f6])).
% 3.75/1.00  
% 3.75/1.00  fof(f60,plain,(
% 3.75/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f25])).
% 3.75/1.00  
% 3.75/1.00  fof(f4,axiom,(
% 3.75/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f23,plain,(
% 3.75/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.75/1.00    inference(ennf_transformation,[],[f4])).
% 3.75/1.00  
% 3.75/1.00  fof(f58,plain,(
% 3.75/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f23])).
% 3.75/1.00  
% 3.75/1.00  fof(f3,axiom,(
% 3.75/1.00    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f22,plain,(
% 3.75/1.00    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.75/1.00    inference(ennf_transformation,[],[f3])).
% 3.75/1.00  
% 3.75/1.00  fof(f57,plain,(
% 3.75/1.00    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f22])).
% 3.75/1.00  
% 3.75/1.00  fof(f9,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f29,plain,(
% 3.75/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f9])).
% 3.75/1.00  
% 3.75/1.00  fof(f30,plain,(
% 3.75/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/1.00    inference(flattening,[],[f29])).
% 3.75/1.00  
% 3.75/1.00  fof(f65,plain,(
% 3.75/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f30])).
% 3.75/1.00  
% 3.75/1.00  fof(f10,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f31,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f10])).
% 3.75/1.00  
% 3.75/1.00  fof(f32,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/1.00    inference(flattening,[],[f31])).
% 3.75/1.00  
% 3.75/1.00  fof(f44,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/1.00    inference(nnf_transformation,[],[f32])).
% 3.75/1.00  
% 3.75/1.00  fof(f45,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/1.00    inference(flattening,[],[f44])).
% 3.75/1.00  
% 3.75/1.00  fof(f67,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f45])).
% 3.75/1.00  
% 3.75/1.00  fof(f95,plain,(
% 3.75/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/1.00    inference(equality_resolution,[],[f67])).
% 3.75/1.00  
% 3.75/1.00  fof(f11,axiom,(
% 3.75/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f33,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.75/1.00    inference(ennf_transformation,[],[f11])).
% 3.75/1.00  
% 3.75/1.00  fof(f69,plain,(
% 3.75/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f33])).
% 3.75/1.00  
% 3.75/1.00  fof(f13,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f36,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f13])).
% 3.75/1.00  
% 3.75/1.00  fof(f37,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.75/1.00    inference(flattening,[],[f36])).
% 3.75/1.00  
% 3.75/1.00  fof(f71,plain,(
% 3.75/1.00    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f37])).
% 3.75/1.00  
% 3.75/1.00  fof(f75,plain,(
% 3.75/1.00    ~v2_struct_0(sK0)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f81,plain,(
% 3.75/1.00    ~v2_struct_0(sK2)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f12,axiom,(
% 3.75/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f34,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.75/1.00    inference(ennf_transformation,[],[f12])).
% 3.75/1.00  
% 3.75/1.00  fof(f35,plain,(
% 3.75/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.75/1.00    inference(flattening,[],[f34])).
% 3.75/1.00  
% 3.75/1.00  fof(f70,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f35])).
% 3.75/1.00  
% 3.75/1.00  fof(f93,plain,(
% 3.75/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f89,plain,(
% 3.75/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f87,plain,(
% 3.75/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f86,plain,(
% 3.75/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f85,plain,(
% 3.75/1.00    v1_funct_1(sK4)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f83,plain,(
% 3.75/1.00    ~v2_struct_0(sK3)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f80,plain,(
% 3.75/1.00    l1_pre_topc(sK1)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f79,plain,(
% 3.75/1.00    v2_pre_topc(sK1)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f78,plain,(
% 3.75/1.00    ~v2_struct_0(sK1)),
% 3.75/1.00    inference(cnf_transformation,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  cnf(c_21,negated_conjecture,
% 3.75/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.75/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1138,plain,
% 3.75/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_22,negated_conjecture,
% 3.75/1.00      ( sK5 = sK6 ),
% 3.75/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1202,plain,
% 3.75/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.75/1.00      inference(light_normalisation,[status(thm)],[c_1138,c_22]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_18,plain,
% 3.75/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.75/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.75/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.75/1.00      | ~ v1_tsep_1(X4,X0)
% 3.75/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.75/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.75/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.75/1.00      | ~ m1_pre_topc(X4,X5)
% 3.75/1.00      | ~ m1_pre_topc(X0,X5)
% 3.75/1.00      | ~ m1_pre_topc(X4,X0)
% 3.75/1.00      | ~ v1_funct_1(X2)
% 3.75/1.00      | v2_struct_0(X5)
% 3.75/1.00      | v2_struct_0(X1)
% 3.75/1.00      | v2_struct_0(X4)
% 3.75/1.00      | v2_struct_0(X0)
% 3.75/1.00      | ~ v2_pre_topc(X5)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | ~ l1_pre_topc(X5)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1141,plain,
% 3.75/1.00      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.75/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.75/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.75/1.00      | v1_tsep_1(X4,X0) != iProver_top
% 3.75/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.75/1.00      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.75/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.75/1.00      | m1_pre_topc(X4,X5) != iProver_top
% 3.75/1.00      | m1_pre_topc(X0,X5) != iProver_top
% 3.75/1.00      | m1_pre_topc(X4,X0) != iProver_top
% 3.75/1.00      | v1_funct_1(X2) != iProver_top
% 3.75/1.00      | v2_struct_0(X5) = iProver_top
% 3.75/1.00      | v2_struct_0(X1) = iProver_top
% 3.75/1.00      | v2_struct_0(X4) = iProver_top
% 3.75/1.00      | v2_struct_0(X0) = iProver_top
% 3.75/1.00      | v2_pre_topc(X5) != iProver_top
% 3.75/1.00      | v2_pre_topc(X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X5) != iProver_top
% 3.75/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_17,plain,
% 3.75/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | ~ m1_pre_topc(X2,X0)
% 3.75/1.00      | m1_pre_topc(X2,X1)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1142,plain,
% 3.75/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.75/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.75/1.00      | m1_pre_topc(X2,X1) = iProver_top
% 3.75/1.00      | v2_pre_topc(X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1380,plain,
% 3.75/1.00      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.75/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.75/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.75/1.00      | v1_tsep_1(X4,X0) != iProver_top
% 3.75/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.75/1.00      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.75/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.75/1.00      | m1_pre_topc(X0,X5) != iProver_top
% 3.75/1.00      | m1_pre_topc(X4,X0) != iProver_top
% 3.75/1.00      | v1_funct_1(X2) != iProver_top
% 3.75/1.00      | v2_struct_0(X5) = iProver_top
% 3.75/1.00      | v2_struct_0(X1) = iProver_top
% 3.75/1.00      | v2_struct_0(X4) = iProver_top
% 3.75/1.00      | v2_struct_0(X0) = iProver_top
% 3.75/1.00      | v2_pre_topc(X5) != iProver_top
% 3.75/1.00      | v2_pre_topc(X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X5) != iProver_top
% 3.75/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.75/1.00      inference(forward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_1141,c_1142]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6399,plain,
% 3.75/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.75/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.75/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.75/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.75/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.75/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.75/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.75/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.75/1.00      | v1_funct_1(sK4) != iProver_top
% 3.75/1.00      | v2_struct_0(sK0) = iProver_top
% 3.75/1.00      | v2_struct_0(sK2) = iProver_top
% 3.75/1.00      | v2_struct_0(sK1) = iProver_top
% 3.75/1.00      | v2_struct_0(sK3) = iProver_top
% 3.75/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.75/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_1202,c_1380]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_29,negated_conjecture,
% 3.75/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1132,plain,
% 3.75/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4,plain,
% 3.75/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1152,plain,
% 3.75/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2561,plain,
% 3.75/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_1132,c_1152]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_36,negated_conjecture,
% 3.75/1.00      ( l1_pre_topc(sK0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_41,plain,
% 3.75/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1812,plain,
% 3.75/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.75/1.00      inference(resolution,[status(thm)],[c_4,c_29]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1813,plain,
% 3.75/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2766,plain,
% 3.75/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_2561,c_41,c_1813]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_0,plain,
% 3.75/1.00      ( ~ l1_pre_topc(X0)
% 3.75/1.00      | ~ v1_pre_topc(X0)
% 3.75/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1156,plain,
% 3.75/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.75/1.00      | l1_pre_topc(X0) != iProver_top
% 3.75/1.00      | v1_pre_topc(X0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3142,plain,
% 3.75/1.00      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
% 3.75/1.00      | v1_pre_topc(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_2766,c_1156]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_37,negated_conjecture,
% 3.75/1.00      ( v2_pre_topc(sK0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_40,plain,
% 3.75/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_31,negated_conjecture,
% 3.75/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1814,plain,
% 3.75/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.75/1.00      inference(resolution,[status(thm)],[c_4,c_31]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1815,plain,
% 3.75/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1,plain,
% 3.75/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | v2_pre_topc(X0)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2809,plain,
% 3.75/1.00      ( ~ v2_pre_topc(sK0) | v2_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 3.75/1.00      inference(resolution,[status(thm)],[c_1,c_31]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2810,plain,
% 3.75/1.00      ( v2_pre_topc(sK0) != iProver_top
% 3.75/1.00      | v2_pre_topc(sK2) = iProver_top
% 3.75/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2809]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_25,negated_conjecture,
% 3.75/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.75/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_7,plain,
% 3.75/1.00      ( ~ v2_pre_topc(X0)
% 3.75/1.00      | ~ l1_pre_topc(X0)
% 3.75/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.75/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1149,plain,
% 3.75/1.00      ( v2_pre_topc(X0) != iProver_top
% 3.75/1.00      | l1_pre_topc(X0) != iProver_top
% 3.75/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3269,plain,
% 3.75/1.00      ( v2_pre_topc(sK2) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.75/1.00      | v1_pre_topc(sK3) = iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_25,c_1149]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3514,plain,
% 3.75/1.00      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_3142,c_40,c_41,c_1815,c_2810,c_3269]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_9,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.75/1.00      | X2 = X1
% 3.75/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1147,plain,
% 3.75/1.00      ( X0 = X1
% 3.75/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.75/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4061,plain,
% 3.75/1.00      ( g1_pre_topc(X0,X1) != sK3
% 3.75/1.00      | u1_struct_0(sK2) = X0
% 3.75/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_25,c_1147]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5,plain,
% 3.75/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.75/1.00      | ~ l1_pre_topc(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2978,plain,
% 3.75/1.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.75/1.00      | ~ l1_pre_topc(sK2) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2983,plain,
% 3.75/1.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 3.75/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2978]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4063,plain,
% 3.75/1.00      ( g1_pre_topc(X0,X1) != sK3
% 3.75/1.00      | u1_struct_0(sK2) = X0
% 3.75/1.00      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_25,c_1147]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4210,plain,
% 3.75/1.00      ( u1_struct_0(sK2) = X0 | g1_pre_topc(X0,X1) != sK3 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_4061,c_41,c_1815,c_2983,c_4063]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4211,plain,
% 3.75/1.00      ( g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK2) = X0 ),
% 3.75/1.00      inference(renaming,[status(thm)],[c_4210]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4216,plain,
% 3.75/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_3514,c_4211]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6417,plain,
% 3.75/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.75/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.75/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.75/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.75/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.75/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.75/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.75/1.00      | v1_funct_1(sK4) != iProver_top
% 3.75/1.00      | v2_struct_0(sK0) = iProver_top
% 3.75/1.00      | v2_struct_0(sK2) = iProver_top
% 3.75/1.00      | v2_struct_0(sK1) = iProver_top
% 3.75/1.00      | v2_struct_0(sK3) = iProver_top
% 3.75/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.75/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.75/1.00      inference(light_normalisation,[status(thm)],[c_6399,c_4216]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3,plain,
% 3.75/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1153,plain,
% 3.75/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2771,plain,
% 3.75/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_2766,c_1153]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2,plain,
% 3.75/1.00      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1154,plain,
% 3.75/1.00      ( k2_struct_0(X0) = u1_struct_0(X0)
% 3.75/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2906,plain,
% 3.75/1.00      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_2771,c_1154]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_10,plain,
% 3.75/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.75/1.00      | ~ v2_pre_topc(X0)
% 3.75/1.00      | ~ l1_pre_topc(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1146,plain,
% 3.75/1.00      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 3.75/1.00      | v2_pre_topc(X0) != iProver_top
% 3.75/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3612,plain,
% 3.75/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
% 3.75/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_2906,c_1146]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2807,plain,
% 3.75/1.00      ( ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 3.75/1.00      inference(resolution,[status(thm)],[c_1,c_29]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2808,plain,
% 3.75/1.00      ( v2_pre_topc(sK0) != iProver_top
% 3.75/1.00      | v2_pre_topc(sK3) = iProver_top
% 3.75/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2807]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5700,plain,
% 3.75/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_3612,c_40,c_41,c_1813,c_2808]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_12,plain,
% 3.75/1.00      ( v1_tsep_1(X0,X1)
% 3.75/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.75/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.75/1.00      | ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_14,plain,
% 3.75/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.75/1.00      | ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_280,plain,
% 3.75/1.00      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.75/1.00      | v1_tsep_1(X0,X1)
% 3.75/1.00      | ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_12,c_14]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_281,plain,
% 3.75/1.00      ( v1_tsep_1(X0,X1)
% 3.75/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.75/1.00      | ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(renaming,[status(thm)],[c_280]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1122,plain,
% 3.75/1.00      ( v1_tsep_1(X0,X1) = iProver_top
% 3.75/1.00      | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 3.75/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 3.75/1.00      | v2_pre_topc(X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4340,plain,
% 3.75/1.00      ( v1_tsep_1(sK2,X0) = iProver_top
% 3.75/1.00      | v3_pre_topc(u1_struct_0(sK3),X0) != iProver_top
% 3.75/1.00      | m1_pre_topc(sK2,X0) != iProver_top
% 3.75/1.00      | v2_pre_topc(X0) != iProver_top
% 3.75/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_4216,c_1122]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6159,plain,
% 3.75/1.00      ( v1_tsep_1(sK2,sK3) = iProver_top
% 3.75/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.75/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_5700,c_4340]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1130,plain,
% 3.75/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_16,plain,
% 3.75/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | v2_struct_0(X1)
% 3.75/1.00      | v2_struct_0(X0)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | ~ l1_pre_topc(X1)
% 3.75/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1143,plain,
% 3.75/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 3.75/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 3.75/1.00      | v2_struct_0(X1) = iProver_top
% 3.75/1.00      | v2_struct_0(X0) = iProver_top
% 3.75/1.00      | v2_pre_topc(X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3738,plain,
% 3.75/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 3.75/1.00      | v2_struct_0(sK0) = iProver_top
% 3.75/1.00      | v2_struct_0(sK2) = iProver_top
% 3.75/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_1130,c_1143]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3744,plain,
% 3.75/1.00      ( k1_tsep_1(sK0,sK2,sK2) = sK3
% 3.75/1.00      | v2_struct_0(sK0) = iProver_top
% 3.75/1.00      | v2_struct_0(sK2) = iProver_top
% 3.75/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.75/1.00      inference(light_normalisation,[status(thm)],[c_3738,c_25]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_38,negated_conjecture,
% 3.75/1.00      ( ~ v2_struct_0(sK0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_39,plain,
% 3.75/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_32,negated_conjecture,
% 3.75/1.00      ( ~ v2_struct_0(sK2) ),
% 3.75/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_45,plain,
% 3.75/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4228,plain,
% 3.75/1.00      ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_3744,c_39,c_40,c_41,c_45]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_15,plain,
% 3.75/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.75/1.00      | ~ m1_pre_topc(X2,X1)
% 3.75/1.00      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 3.75/1.00      | v2_struct_0(X1)
% 3.75/1.00      | v2_struct_0(X0)
% 3.75/1.00      | v2_struct_0(X2)
% 3.75/1.00      | ~ v2_pre_topc(X1)
% 3.75/1.00      | ~ l1_pre_topc(X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1144,plain,
% 3.75/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.75/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.75/1.00      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
% 3.75/1.00      | v2_struct_0(X1) = iProver_top
% 3.75/1.00      | v2_struct_0(X0) = iProver_top
% 3.75/1.00      | v2_struct_0(X2) = iProver_top
% 3.75/1.00      | v2_pre_topc(X1) != iProver_top
% 3.75/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4646,plain,
% 3.75/1.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.75/1.00      | m1_pre_topc(sK2,sK3) = iProver_top
% 3.75/1.00      | v2_struct_0(sK0) = iProver_top
% 3.75/1.00      | v2_struct_0(sK2) = iProver_top
% 3.75/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.75/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_4228,c_1144]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_20,negated_conjecture,
% 3.75/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.75/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_55,plain,
% 3.75/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_24,negated_conjecture,
% 3.75/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.75/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_52,plain,
% 3.75/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_26,negated_conjecture,
% 3.75/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.75/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_51,plain,
% 3.75/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_27,negated_conjecture,
% 3.75/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.75/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_50,plain,
% 3.75/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_28,negated_conjecture,
% 3.75/1.00      ( v1_funct_1(sK4) ),
% 3.75/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_49,plain,
% 3.75/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_48,plain,
% 3.75/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_30,negated_conjecture,
% 3.75/1.00      ( ~ v2_struct_0(sK3) ),
% 3.75/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_47,plain,
% 3.75/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_46,plain,
% 3.75/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_33,negated_conjecture,
% 3.75/1.00      ( l1_pre_topc(sK1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_44,plain,
% 3.75/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_34,negated_conjecture,
% 3.75/1.00      ( v2_pre_topc(sK1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_43,plain,
% 3.75/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_35,negated_conjecture,
% 3.75/1.00      ( ~ v2_struct_0(sK1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_42,plain,
% 3.75/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(contradiction,plain,
% 3.75/1.00      ( $false ),
% 3.75/1.00      inference(minisat,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_6417,c_6159,c_4646,c_2808,c_1813,c_55,c_52,c_51,c_50,
% 3.75/1.00                 c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42,c_41,c_40,c_39]) ).
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  ------                               Statistics
% 3.75/1.00  
% 3.75/1.00  ------ Selected
% 3.75/1.00  
% 3.75/1.00  total_time:                             0.258
% 3.75/1.01  
%------------------------------------------------------------------------------
