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
% DateTime   : Thu Dec  3 12:23:29 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 775 expanded)
%              Number of clauses        :  109 ( 168 expanded)
%              Number of leaves         :   22 ( 341 expanded)
%              Depth                    :   28
%              Number of atoms          : 1131 (10922 expanded)
%              Number of equality atoms :  284 (1637 expanded)
%              Maximal formula depth    :   31 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f15])).

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

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
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
            ( ~ r1_tmap_1(X3,X1,X4,sK6)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
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
                ( ~ r1_tmap_1(X3,X1,sK5,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
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
                    ( ~ r1_tmap_1(sK4,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
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
                        & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
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
                            ( ~ r1_tmap_1(X3,sK2,X4,X5)
                            & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f49,f48,f47,f46,f45,f44,f43])).

fof(f81,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f40])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f79,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f64,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1618,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3346,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1618])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2257,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2767,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_2768,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2767])).

cnf(c_1605,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1621,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2825,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1621])).

cnf(c_3349,plain,
    ( v1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3346,c_37,c_38,c_43,c_2768,c_2825])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1607,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2824,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1621])).

cnf(c_2914,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2824,c_38])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1623,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2919,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | v1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2914,c_1623])).

cnf(c_3354,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_3349,c_2919])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1616,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3664,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1616])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2906,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2911,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2906])).

cnf(c_3666,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0
    | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1616])).

cnf(c_3792,plain,
    ( u1_struct_0(sK3) = X0
    | g1_pre_topc(X0,X1) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3664,c_38,c_2825,c_2911,c_3666])).

cnf(c_3793,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0 ),
    inference(renaming,[status(thm)],[c_3792])).

cnf(c_3798,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3354,c_3793])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1611,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1661,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1611,c_19])).

cnf(c_12,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
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
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_456,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
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
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_457,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_461,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_25])).

cnf(c_462,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_461])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_509,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_462,c_14])).

cnf(c_533,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X5 != X6
    | u1_struct_0(X0) != X7
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_509])).

cnf(c_534,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_755,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X3 != X6
    | X4 != X5
    | sK0(X6,X5) != X7
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_534])).

cnf(c_756,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | sK0(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_781,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_756,c_668])).

cnf(c_802,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_781,c_3,c_2])).

cnf(c_1594,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK0(X1,X4),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_1994,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1594])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_40,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2508,plain,
    ( l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1994,c_39,c_40,c_41])).

cnf(c_2509,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2508])).

cnf(c_2526,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2509])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_44,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3151,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2526,c_44,c_48])).

cnf(c_3152,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3151])).

cnf(c_3168,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_3152])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_49,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_52,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1610,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1648,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1610,c_19])).

cnf(c_3171,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3168,c_36,c_37,c_38,c_42,c_45,c_49,c_52,c_1648])).

cnf(c_4114,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3798,c_3171])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1614,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_186,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_3])).

cnf(c_187,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_1597,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_3225,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1597])).

cnf(c_3237,plain,
    ( m1_pre_topc(X0,sK4) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3225,c_38,c_2825])).

cnf(c_3238,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3237])).

cnf(c_3245,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_3238])).

cnf(c_2271,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2794,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_2795,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_1937,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_1938,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1937])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4114,c_3245,c_2825,c_2824,c_2795,c_1938,c_49,c_45,c_44,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.92/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/0.99  
% 2.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.99  
% 2.92/0.99  ------  iProver source info
% 2.92/0.99  
% 2.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.99  git: non_committed_changes: false
% 2.92/0.99  git: last_make_outside_of_git: false
% 2.92/0.99  
% 2.92/0.99  ------ 
% 2.92/0.99  
% 2.92/0.99  ------ Input Options
% 2.92/0.99  
% 2.92/0.99  --out_options                           all
% 2.92/0.99  --tptp_safe_out                         true
% 2.92/0.99  --problem_path                          ""
% 2.92/0.99  --include_path                          ""
% 2.92/0.99  --clausifier                            res/vclausify_rel
% 2.92/0.99  --clausifier_options                    --mode clausify
% 2.92/0.99  --stdin                                 false
% 2.92/0.99  --stats_out                             all
% 2.92/0.99  
% 2.92/0.99  ------ General Options
% 2.92/0.99  
% 2.92/0.99  --fof                                   false
% 2.92/0.99  --time_out_real                         305.
% 2.92/0.99  --time_out_virtual                      -1.
% 2.92/0.99  --symbol_type_check                     false
% 2.92/0.99  --clausify_out                          false
% 2.92/0.99  --sig_cnt_out                           false
% 2.92/0.99  --trig_cnt_out                          false
% 2.92/0.99  --trig_cnt_out_tolerance                1.
% 2.92/0.99  --trig_cnt_out_sk_spl                   false
% 2.92/0.99  --abstr_cl_out                          false
% 2.92/0.99  
% 2.92/0.99  ------ Global Options
% 2.92/0.99  
% 2.92/0.99  --schedule                              default
% 2.92/0.99  --add_important_lit                     false
% 2.92/0.99  --prop_solver_per_cl                    1000
% 2.92/0.99  --min_unsat_core                        false
% 2.92/0.99  --soft_assumptions                      false
% 2.92/0.99  --soft_lemma_size                       3
% 2.92/0.99  --prop_impl_unit_size                   0
% 2.92/0.99  --prop_impl_unit                        []
% 2.92/0.99  --share_sel_clauses                     true
% 2.92/0.99  --reset_solvers                         false
% 2.92/0.99  --bc_imp_inh                            [conj_cone]
% 2.92/0.99  --conj_cone_tolerance                   3.
% 2.92/0.99  --extra_neg_conj                        none
% 2.92/0.99  --large_theory_mode                     true
% 2.92/0.99  --prolific_symb_bound                   200
% 2.92/0.99  --lt_threshold                          2000
% 2.92/0.99  --clause_weak_htbl                      true
% 2.92/0.99  --gc_record_bc_elim                     false
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing Options
% 2.92/1.00  
% 2.92/1.00  --preprocessing_flag                    true
% 2.92/1.00  --time_out_prep_mult                    0.1
% 2.92/1.00  --splitting_mode                        input
% 2.92/1.00  --splitting_grd                         true
% 2.92/1.00  --splitting_cvd                         false
% 2.92/1.00  --splitting_cvd_svl                     false
% 2.92/1.00  --splitting_nvd                         32
% 2.92/1.00  --sub_typing                            true
% 2.92/1.00  --prep_gs_sim                           true
% 2.92/1.00  --prep_unflatten                        true
% 2.92/1.00  --prep_res_sim                          true
% 2.92/1.00  --prep_upred                            true
% 2.92/1.00  --prep_sem_filter                       exhaustive
% 2.92/1.00  --prep_sem_filter_out                   false
% 2.92/1.00  --pred_elim                             true
% 2.92/1.00  --res_sim_input                         true
% 2.92/1.00  --eq_ax_congr_red                       true
% 2.92/1.00  --pure_diseq_elim                       true
% 2.92/1.00  --brand_transform                       false
% 2.92/1.00  --non_eq_to_eq                          false
% 2.92/1.00  --prep_def_merge                        true
% 2.92/1.00  --prep_def_merge_prop_impl              false
% 2.92/1.00  --prep_def_merge_mbd                    true
% 2.92/1.00  --prep_def_merge_tr_red                 false
% 2.92/1.00  --prep_def_merge_tr_cl                  false
% 2.92/1.00  --smt_preprocessing                     true
% 2.92/1.00  --smt_ac_axioms                         fast
% 2.92/1.00  --preprocessed_out                      false
% 2.92/1.00  --preprocessed_stats                    false
% 2.92/1.00  
% 2.92/1.00  ------ Abstraction refinement Options
% 2.92/1.00  
% 2.92/1.00  --abstr_ref                             []
% 2.92/1.00  --abstr_ref_prep                        false
% 2.92/1.00  --abstr_ref_until_sat                   false
% 2.92/1.00  --abstr_ref_sig_restrict                funpre
% 2.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/1.00  --abstr_ref_under                       []
% 2.92/1.00  
% 2.92/1.00  ------ SAT Options
% 2.92/1.00  
% 2.92/1.00  --sat_mode                              false
% 2.92/1.00  --sat_fm_restart_options                ""
% 2.92/1.00  --sat_gr_def                            false
% 2.92/1.00  --sat_epr_types                         true
% 2.92/1.00  --sat_non_cyclic_types                  false
% 2.92/1.00  --sat_finite_models                     false
% 2.92/1.00  --sat_fm_lemmas                         false
% 2.92/1.00  --sat_fm_prep                           false
% 2.92/1.00  --sat_fm_uc_incr                        true
% 2.92/1.00  --sat_out_model                         small
% 2.92/1.00  --sat_out_clauses                       false
% 2.92/1.00  
% 2.92/1.00  ------ QBF Options
% 2.92/1.00  
% 2.92/1.00  --qbf_mode                              false
% 2.92/1.00  --qbf_elim_univ                         false
% 2.92/1.00  --qbf_dom_inst                          none
% 2.92/1.00  --qbf_dom_pre_inst                      false
% 2.92/1.00  --qbf_sk_in                             false
% 2.92/1.00  --qbf_pred_elim                         true
% 2.92/1.00  --qbf_split                             512
% 2.92/1.00  
% 2.92/1.00  ------ BMC1 Options
% 2.92/1.00  
% 2.92/1.00  --bmc1_incremental                      false
% 2.92/1.00  --bmc1_axioms                           reachable_all
% 2.92/1.00  --bmc1_min_bound                        0
% 2.92/1.00  --bmc1_max_bound                        -1
% 2.92/1.00  --bmc1_max_bound_default                -1
% 2.92/1.00  --bmc1_symbol_reachability              true
% 2.92/1.00  --bmc1_property_lemmas                  false
% 2.92/1.00  --bmc1_k_induction                      false
% 2.92/1.00  --bmc1_non_equiv_states                 false
% 2.92/1.00  --bmc1_deadlock                         false
% 2.92/1.00  --bmc1_ucm                              false
% 2.92/1.00  --bmc1_add_unsat_core                   none
% 2.92/1.00  --bmc1_unsat_core_children              false
% 2.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/1.00  --bmc1_out_stat                         full
% 2.92/1.00  --bmc1_ground_init                      false
% 2.92/1.00  --bmc1_pre_inst_next_state              false
% 2.92/1.00  --bmc1_pre_inst_state                   false
% 2.92/1.00  --bmc1_pre_inst_reach_state             false
% 2.92/1.00  --bmc1_out_unsat_core                   false
% 2.92/1.00  --bmc1_aig_witness_out                  false
% 2.92/1.00  --bmc1_verbose                          false
% 2.92/1.00  --bmc1_dump_clauses_tptp                false
% 2.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.92/1.00  --bmc1_dump_file                        -
% 2.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.92/1.00  --bmc1_ucm_extend_mode                  1
% 2.92/1.00  --bmc1_ucm_init_mode                    2
% 2.92/1.00  --bmc1_ucm_cone_mode                    none
% 2.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.92/1.00  --bmc1_ucm_relax_model                  4
% 2.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/1.00  --bmc1_ucm_layered_model                none
% 2.92/1.00  --bmc1_ucm_max_lemma_size               10
% 2.92/1.00  
% 2.92/1.00  ------ AIG Options
% 2.92/1.00  
% 2.92/1.00  --aig_mode                              false
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation Options
% 2.92/1.00  
% 2.92/1.00  --instantiation_flag                    true
% 2.92/1.00  --inst_sos_flag                         false
% 2.92/1.00  --inst_sos_phase                        true
% 2.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel_side                     num_symb
% 2.92/1.00  --inst_solver_per_active                1400
% 2.92/1.00  --inst_solver_calls_frac                1.
% 2.92/1.00  --inst_passive_queue_type               priority_queues
% 2.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/1.00  --inst_passive_queues_freq              [25;2]
% 2.92/1.00  --inst_dismatching                      true
% 2.92/1.00  --inst_eager_unprocessed_to_passive     true
% 2.92/1.00  --inst_prop_sim_given                   true
% 2.92/1.00  --inst_prop_sim_new                     false
% 2.92/1.00  --inst_subs_new                         false
% 2.92/1.00  --inst_eq_res_simp                      false
% 2.92/1.00  --inst_subs_given                       false
% 2.92/1.00  --inst_orphan_elimination               true
% 2.92/1.00  --inst_learning_loop_flag               true
% 2.92/1.00  --inst_learning_start                   3000
% 2.92/1.00  --inst_learning_factor                  2
% 2.92/1.00  --inst_start_prop_sim_after_learn       3
% 2.92/1.00  --inst_sel_renew                        solver
% 2.92/1.00  --inst_lit_activity_flag                true
% 2.92/1.00  --inst_restr_to_given                   false
% 2.92/1.00  --inst_activity_threshold               500
% 2.92/1.00  --inst_out_proof                        true
% 2.92/1.00  
% 2.92/1.00  ------ Resolution Options
% 2.92/1.00  
% 2.92/1.00  --resolution_flag                       true
% 2.92/1.00  --res_lit_sel                           adaptive
% 2.92/1.00  --res_lit_sel_side                      none
% 2.92/1.00  --res_ordering                          kbo
% 2.92/1.00  --res_to_prop_solver                    active
% 2.92/1.00  --res_prop_simpl_new                    false
% 2.92/1.00  --res_prop_simpl_given                  true
% 2.92/1.00  --res_passive_queue_type                priority_queues
% 2.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/1.00  --res_passive_queues_freq               [15;5]
% 2.92/1.00  --res_forward_subs                      full
% 2.92/1.00  --res_backward_subs                     full
% 2.92/1.00  --res_forward_subs_resolution           true
% 2.92/1.00  --res_backward_subs_resolution          true
% 2.92/1.00  --res_orphan_elimination                true
% 2.92/1.00  --res_time_limit                        2.
% 2.92/1.00  --res_out_proof                         true
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Options
% 2.92/1.00  
% 2.92/1.00  --superposition_flag                    true
% 2.92/1.00  --sup_passive_queue_type                priority_queues
% 2.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.92/1.00  --demod_completeness_check              fast
% 2.92/1.00  --demod_use_ground                      true
% 2.92/1.00  --sup_to_prop_solver                    passive
% 2.92/1.00  --sup_prop_simpl_new                    true
% 2.92/1.00  --sup_prop_simpl_given                  true
% 2.92/1.00  --sup_fun_splitting                     false
% 2.92/1.00  --sup_smt_interval                      50000
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Simplification Setup
% 2.92/1.00  
% 2.92/1.00  --sup_indices_passive                   []
% 2.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_full_bw                           [BwDemod]
% 2.92/1.00  --sup_immed_triv                        [TrivRules]
% 2.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_immed_bw_main                     []
% 2.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  
% 2.92/1.00  ------ Combination Options
% 2.92/1.00  
% 2.92/1.00  --comb_res_mult                         3
% 2.92/1.00  --comb_sup_mult                         2
% 2.92/1.00  --comb_inst_mult                        10
% 2.92/1.00  
% 2.92/1.00  ------ Debug Options
% 2.92/1.00  
% 2.92/1.00  --dbg_backtrace                         false
% 2.92/1.00  --dbg_dump_prop_clauses                 false
% 2.92/1.00  --dbg_dump_prop_clauses_file            -
% 2.92/1.00  --dbg_out_stat                          false
% 2.92/1.00  ------ Parsing...
% 2.92/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/1.00  ------ Proving...
% 2.92/1.00  ------ Problem Properties 
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  clauses                                 32
% 2.92/1.00  conjectures                             17
% 2.92/1.00  EPR                                     16
% 2.92/1.00  Horn                                    29
% 2.92/1.00  unary                                   17
% 2.92/1.00  binary                                  2
% 2.92/1.00  lits                                    96
% 2.92/1.00  lits eq                                 11
% 2.92/1.00  fd_pure                                 0
% 2.92/1.00  fd_pseudo                               0
% 2.92/1.00  fd_cond                                 0
% 2.92/1.00  fd_pseudo_cond                          2
% 2.92/1.00  AC symbols                              0
% 2.92/1.00  
% 2.92/1.00  ------ Schedule dynamic 5 is on 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ 
% 2.92/1.00  Current options:
% 2.92/1.00  ------ 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options
% 2.92/1.00  
% 2.92/1.00  --out_options                           all
% 2.92/1.00  --tptp_safe_out                         true
% 2.92/1.00  --problem_path                          ""
% 2.92/1.00  --include_path                          ""
% 2.92/1.00  --clausifier                            res/vclausify_rel
% 2.92/1.00  --clausifier_options                    --mode clausify
% 2.92/1.00  --stdin                                 false
% 2.92/1.00  --stats_out                             all
% 2.92/1.00  
% 2.92/1.00  ------ General Options
% 2.92/1.00  
% 2.92/1.00  --fof                                   false
% 2.92/1.00  --time_out_real                         305.
% 2.92/1.00  --time_out_virtual                      -1.
% 2.92/1.00  --symbol_type_check                     false
% 2.92/1.00  --clausify_out                          false
% 2.92/1.00  --sig_cnt_out                           false
% 2.92/1.00  --trig_cnt_out                          false
% 2.92/1.00  --trig_cnt_out_tolerance                1.
% 2.92/1.00  --trig_cnt_out_sk_spl                   false
% 2.92/1.00  --abstr_cl_out                          false
% 2.92/1.00  
% 2.92/1.00  ------ Global Options
% 2.92/1.00  
% 2.92/1.00  --schedule                              default
% 2.92/1.00  --add_important_lit                     false
% 2.92/1.00  --prop_solver_per_cl                    1000
% 2.92/1.00  --min_unsat_core                        false
% 2.92/1.00  --soft_assumptions                      false
% 2.92/1.00  --soft_lemma_size                       3
% 2.92/1.00  --prop_impl_unit_size                   0
% 2.92/1.00  --prop_impl_unit                        []
% 2.92/1.00  --share_sel_clauses                     true
% 2.92/1.00  --reset_solvers                         false
% 2.92/1.00  --bc_imp_inh                            [conj_cone]
% 2.92/1.00  --conj_cone_tolerance                   3.
% 2.92/1.00  --extra_neg_conj                        none
% 2.92/1.00  --large_theory_mode                     true
% 2.92/1.00  --prolific_symb_bound                   200
% 2.92/1.00  --lt_threshold                          2000
% 2.92/1.00  --clause_weak_htbl                      true
% 2.92/1.00  --gc_record_bc_elim                     false
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing Options
% 2.92/1.00  
% 2.92/1.00  --preprocessing_flag                    true
% 2.92/1.00  --time_out_prep_mult                    0.1
% 2.92/1.00  --splitting_mode                        input
% 2.92/1.00  --splitting_grd                         true
% 2.92/1.00  --splitting_cvd                         false
% 2.92/1.00  --splitting_cvd_svl                     false
% 2.92/1.00  --splitting_nvd                         32
% 2.92/1.00  --sub_typing                            true
% 2.92/1.00  --prep_gs_sim                           true
% 2.92/1.00  --prep_unflatten                        true
% 2.92/1.00  --prep_res_sim                          true
% 2.92/1.00  --prep_upred                            true
% 2.92/1.00  --prep_sem_filter                       exhaustive
% 2.92/1.00  --prep_sem_filter_out                   false
% 2.92/1.00  --pred_elim                             true
% 2.92/1.00  --res_sim_input                         true
% 2.92/1.00  --eq_ax_congr_red                       true
% 2.92/1.00  --pure_diseq_elim                       true
% 2.92/1.00  --brand_transform                       false
% 2.92/1.00  --non_eq_to_eq                          false
% 2.92/1.00  --prep_def_merge                        true
% 2.92/1.00  --prep_def_merge_prop_impl              false
% 2.92/1.00  --prep_def_merge_mbd                    true
% 2.92/1.00  --prep_def_merge_tr_red                 false
% 2.92/1.00  --prep_def_merge_tr_cl                  false
% 2.92/1.00  --smt_preprocessing                     true
% 2.92/1.00  --smt_ac_axioms                         fast
% 2.92/1.00  --preprocessed_out                      false
% 2.92/1.00  --preprocessed_stats                    false
% 2.92/1.00  
% 2.92/1.00  ------ Abstraction refinement Options
% 2.92/1.00  
% 2.92/1.00  --abstr_ref                             []
% 2.92/1.00  --abstr_ref_prep                        false
% 2.92/1.00  --abstr_ref_until_sat                   false
% 2.92/1.00  --abstr_ref_sig_restrict                funpre
% 2.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/1.00  --abstr_ref_under                       []
% 2.92/1.00  
% 2.92/1.00  ------ SAT Options
% 2.92/1.00  
% 2.92/1.00  --sat_mode                              false
% 2.92/1.00  --sat_fm_restart_options                ""
% 2.92/1.00  --sat_gr_def                            false
% 2.92/1.00  --sat_epr_types                         true
% 2.92/1.00  --sat_non_cyclic_types                  false
% 2.92/1.00  --sat_finite_models                     false
% 2.92/1.00  --sat_fm_lemmas                         false
% 2.92/1.00  --sat_fm_prep                           false
% 2.92/1.00  --sat_fm_uc_incr                        true
% 2.92/1.00  --sat_out_model                         small
% 2.92/1.00  --sat_out_clauses                       false
% 2.92/1.00  
% 2.92/1.00  ------ QBF Options
% 2.92/1.00  
% 2.92/1.00  --qbf_mode                              false
% 2.92/1.00  --qbf_elim_univ                         false
% 2.92/1.00  --qbf_dom_inst                          none
% 2.92/1.00  --qbf_dom_pre_inst                      false
% 2.92/1.00  --qbf_sk_in                             false
% 2.92/1.00  --qbf_pred_elim                         true
% 2.92/1.00  --qbf_split                             512
% 2.92/1.00  
% 2.92/1.00  ------ BMC1 Options
% 2.92/1.00  
% 2.92/1.00  --bmc1_incremental                      false
% 2.92/1.00  --bmc1_axioms                           reachable_all
% 2.92/1.00  --bmc1_min_bound                        0
% 2.92/1.00  --bmc1_max_bound                        -1
% 2.92/1.00  --bmc1_max_bound_default                -1
% 2.92/1.00  --bmc1_symbol_reachability              true
% 2.92/1.00  --bmc1_property_lemmas                  false
% 2.92/1.00  --bmc1_k_induction                      false
% 2.92/1.00  --bmc1_non_equiv_states                 false
% 2.92/1.00  --bmc1_deadlock                         false
% 2.92/1.00  --bmc1_ucm                              false
% 2.92/1.00  --bmc1_add_unsat_core                   none
% 2.92/1.00  --bmc1_unsat_core_children              false
% 2.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/1.00  --bmc1_out_stat                         full
% 2.92/1.00  --bmc1_ground_init                      false
% 2.92/1.00  --bmc1_pre_inst_next_state              false
% 2.92/1.00  --bmc1_pre_inst_state                   false
% 2.92/1.00  --bmc1_pre_inst_reach_state             false
% 2.92/1.00  --bmc1_out_unsat_core                   false
% 2.92/1.00  --bmc1_aig_witness_out                  false
% 2.92/1.00  --bmc1_verbose                          false
% 2.92/1.00  --bmc1_dump_clauses_tptp                false
% 2.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.92/1.00  --bmc1_dump_file                        -
% 2.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.92/1.00  --bmc1_ucm_extend_mode                  1
% 2.92/1.00  --bmc1_ucm_init_mode                    2
% 2.92/1.00  --bmc1_ucm_cone_mode                    none
% 2.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.92/1.00  --bmc1_ucm_relax_model                  4
% 2.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/1.00  --bmc1_ucm_layered_model                none
% 2.92/1.00  --bmc1_ucm_max_lemma_size               10
% 2.92/1.00  
% 2.92/1.00  ------ AIG Options
% 2.92/1.00  
% 2.92/1.00  --aig_mode                              false
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation Options
% 2.92/1.00  
% 2.92/1.00  --instantiation_flag                    true
% 2.92/1.00  --inst_sos_flag                         false
% 2.92/1.00  --inst_sos_phase                        true
% 2.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel_side                     none
% 2.92/1.00  --inst_solver_per_active                1400
% 2.92/1.00  --inst_solver_calls_frac                1.
% 2.92/1.00  --inst_passive_queue_type               priority_queues
% 2.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/1.00  --inst_passive_queues_freq              [25;2]
% 2.92/1.00  --inst_dismatching                      true
% 2.92/1.00  --inst_eager_unprocessed_to_passive     true
% 2.92/1.00  --inst_prop_sim_given                   true
% 2.92/1.00  --inst_prop_sim_new                     false
% 2.92/1.00  --inst_subs_new                         false
% 2.92/1.00  --inst_eq_res_simp                      false
% 2.92/1.00  --inst_subs_given                       false
% 2.92/1.00  --inst_orphan_elimination               true
% 2.92/1.00  --inst_learning_loop_flag               true
% 2.92/1.00  --inst_learning_start                   3000
% 2.92/1.00  --inst_learning_factor                  2
% 2.92/1.00  --inst_start_prop_sim_after_learn       3
% 2.92/1.00  --inst_sel_renew                        solver
% 2.92/1.00  --inst_lit_activity_flag                true
% 2.92/1.00  --inst_restr_to_given                   false
% 2.92/1.00  --inst_activity_threshold               500
% 2.92/1.00  --inst_out_proof                        true
% 2.92/1.00  
% 2.92/1.00  ------ Resolution Options
% 2.92/1.00  
% 2.92/1.00  --resolution_flag                       false
% 2.92/1.00  --res_lit_sel                           adaptive
% 2.92/1.00  --res_lit_sel_side                      none
% 2.92/1.00  --res_ordering                          kbo
% 2.92/1.00  --res_to_prop_solver                    active
% 2.92/1.00  --res_prop_simpl_new                    false
% 2.92/1.00  --res_prop_simpl_given                  true
% 2.92/1.00  --res_passive_queue_type                priority_queues
% 2.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/1.00  --res_passive_queues_freq               [15;5]
% 2.92/1.00  --res_forward_subs                      full
% 2.92/1.00  --res_backward_subs                     full
% 2.92/1.00  --res_forward_subs_resolution           true
% 2.92/1.00  --res_backward_subs_resolution          true
% 2.92/1.00  --res_orphan_elimination                true
% 2.92/1.00  --res_time_limit                        2.
% 2.92/1.00  --res_out_proof                         true
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Options
% 2.92/1.00  
% 2.92/1.00  --superposition_flag                    true
% 2.92/1.00  --sup_passive_queue_type                priority_queues
% 2.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.92/1.00  --demod_completeness_check              fast
% 2.92/1.00  --demod_use_ground                      true
% 2.92/1.00  --sup_to_prop_solver                    passive
% 2.92/1.00  --sup_prop_simpl_new                    true
% 2.92/1.00  --sup_prop_simpl_given                  true
% 2.92/1.00  --sup_fun_splitting                     false
% 2.92/1.00  --sup_smt_interval                      50000
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Simplification Setup
% 2.92/1.00  
% 2.92/1.00  --sup_indices_passive                   []
% 2.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_full_bw                           [BwDemod]
% 2.92/1.00  --sup_immed_triv                        [TrivRules]
% 2.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_immed_bw_main                     []
% 2.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  
% 2.92/1.00  ------ Combination Options
% 2.92/1.00  
% 2.92/1.00  --comb_res_mult                         3
% 2.92/1.00  --comb_sup_mult                         2
% 2.92/1.00  --comb_inst_mult                        10
% 2.92/1.00  
% 2.92/1.00  ------ Debug Options
% 2.92/1.00  
% 2.92/1.00  --dbg_backtrace                         false
% 2.92/1.00  --dbg_dump_prop_clauses                 false
% 2.92/1.00  --dbg_dump_prop_clauses_file            -
% 2.92/1.00  --dbg_out_stat                          false
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ Proving...
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS status Theorem for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  fof(f14,conjecture,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f15,negated_conjecture,(
% 2.92/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.92/1.00    inference(negated_conjecture,[],[f14])).
% 2.92/1.00  
% 2.92/1.00  fof(f37,plain,(
% 2.92/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f15])).
% 2.92/1.00  
% 2.92/1.00  fof(f38,plain,(
% 2.92/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.92/1.00    inference(flattening,[],[f37])).
% 2.92/1.00  
% 2.92/1.00  fof(f49,plain,(
% 2.92/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f48,plain,(
% 2.92/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f47,plain,(
% 2.92/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK5,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f46,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f45,plain,(
% 2.92/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f44,plain,(
% 2.92/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f43,plain,(
% 2.92/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f50,plain,(
% 2.92/1.00    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f49,f48,f47,f46,f45,f44,f43])).
% 2.92/1.00  
% 2.92/1.00  fof(f81,plain,(
% 2.92/1.00    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f6,axiom,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f24,plain,(
% 2.92/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f6])).
% 2.92/1.00  
% 2.92/1.00  fof(f25,plain,(
% 2.92/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.92/1.00    inference(flattening,[],[f24])).
% 2.92/1.00  
% 2.92/1.00  fof(f56,plain,(
% 2.92/1.00    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f25])).
% 2.92/1.00  
% 2.92/1.00  fof(f69,plain,(
% 2.92/1.00    v2_pre_topc(sK1)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f70,plain,(
% 2.92/1.00    l1_pre_topc(sK1)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f75,plain,(
% 2.92/1.00    m1_pre_topc(sK3,sK1)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f3,axiom,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f20,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f3])).
% 2.92/1.00  
% 2.92/1.00  fof(f21,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.92/1.00    inference(flattening,[],[f20])).
% 2.92/1.00  
% 2.92/1.00  fof(f53,plain,(
% 2.92/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f21])).
% 2.92/1.00  
% 2.92/1.00  fof(f4,axiom,(
% 2.92/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f22,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f4])).
% 2.92/1.00  
% 2.92/1.00  fof(f54,plain,(
% 2.92/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f22])).
% 2.92/1.00  
% 2.92/1.00  fof(f77,plain,(
% 2.92/1.00    m1_pre_topc(sK4,sK1)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f2,axiom,(
% 2.92/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f18,plain,(
% 2.92/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f2])).
% 2.92/1.00  
% 2.92/1.00  fof(f19,plain,(
% 2.92/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(flattening,[],[f18])).
% 2.92/1.00  
% 2.92/1.00  fof(f52,plain,(
% 2.92/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f19])).
% 2.92/1.00  
% 2.92/1.00  fof(f7,axiom,(
% 2.92/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f26,plain,(
% 2.92/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.92/1.00    inference(ennf_transformation,[],[f7])).
% 2.92/1.00  
% 2.92/1.00  fof(f58,plain,(
% 2.92/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f26])).
% 2.92/1.00  
% 2.92/1.00  fof(f5,axiom,(
% 2.92/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f23,plain,(
% 2.92/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f5])).
% 2.92/1.00  
% 2.92/1.00  fof(f55,plain,(
% 2.92/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f23])).
% 2.92/1.00  
% 2.92/1.00  fof(f85,plain,(
% 2.92/1.00    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f84,plain,(
% 2.92/1.00    sK6 = sK7),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f10,axiom,(
% 2.92/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f30,plain,(
% 2.92/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f10])).
% 2.92/1.00  
% 2.92/1.00  fof(f31,plain,(
% 2.92/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(flattening,[],[f30])).
% 2.92/1.00  
% 2.92/1.00  fof(f40,plain,(
% 2.92/1.00    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f41,plain,(
% 2.92/1.00    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f40])).
% 2.92/1.00  
% 2.92/1.00  fof(f63,plain,(
% 2.92/1.00    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f41])).
% 2.92/1.00  
% 2.92/1.00  fof(f1,axiom,(
% 2.92/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f16,plain,(
% 2.92/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.92/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.92/1.00  
% 2.92/1.00  fof(f17,plain,(
% 2.92/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.92/1.00    inference(ennf_transformation,[],[f16])).
% 2.92/1.00  
% 2.92/1.00  fof(f51,plain,(
% 2.92/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f17])).
% 2.92/1.00  
% 2.92/1.00  fof(f13,axiom,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f35,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f13])).
% 2.92/1.00  
% 2.92/1.00  fof(f36,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(flattening,[],[f35])).
% 2.92/1.00  
% 2.92/1.00  fof(f42,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(nnf_transformation,[],[f36])).
% 2.92/1.00  
% 2.92/1.00  fof(f67,plain,(
% 2.92/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f42])).
% 2.92/1.00  
% 2.92/1.00  fof(f87,plain,(
% 2.92/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.92/1.00    inference(equality_resolution,[],[f67])).
% 2.92/1.00  
% 2.92/1.00  fof(f79,plain,(
% 2.92/1.00    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f78,plain,(
% 2.92/1.00    v1_funct_1(sK5)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f12,axiom,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f33,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f12])).
% 2.92/1.00  
% 2.92/1.00  fof(f34,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.92/1.00    inference(flattening,[],[f33])).
% 2.92/1.00  
% 2.92/1.00  fof(f65,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f34])).
% 2.92/1.00  
% 2.92/1.00  fof(f9,axiom,(
% 2.92/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f28,plain,(
% 2.92/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f9])).
% 2.92/1.00  
% 2.92/1.00  fof(f29,plain,(
% 2.92/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(flattening,[],[f28])).
% 2.92/1.00  
% 2.92/1.00  fof(f62,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f29])).
% 2.92/1.00  
% 2.92/1.00  fof(f71,plain,(
% 2.92/1.00    ~v2_struct_0(sK2)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f72,plain,(
% 2.92/1.00    v2_pre_topc(sK2)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f73,plain,(
% 2.92/1.00    l1_pre_topc(sK2)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f76,plain,(
% 2.92/1.00    ~v2_struct_0(sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f80,plain,(
% 2.92/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f68,plain,(
% 2.92/1.00    ~v2_struct_0(sK1)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f74,plain,(
% 2.92/1.00    ~v2_struct_0(sK3)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f82,plain,(
% 2.92/1.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f86,plain,(
% 2.92/1.00    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f83,plain,(
% 2.92/1.00    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.92/1.00    inference(cnf_transformation,[],[f50])).
% 2.92/1.00  
% 2.92/1.00  fof(f11,axiom,(
% 2.92/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f32,plain,(
% 2.92/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f11])).
% 2.92/1.00  
% 2.92/1.00  fof(f64,plain,(
% 2.92/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f32])).
% 2.92/1.00  
% 2.92/1.00  fof(f8,axiom,(
% 2.92/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f27,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f8])).
% 2.92/1.00  
% 2.92/1.00  fof(f39,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(nnf_transformation,[],[f27])).
% 2.92/1.00  
% 2.92/1.00  fof(f60,plain,(
% 2.92/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f39])).
% 2.92/1.00  
% 2.92/1.00  cnf(c_22,negated_conjecture,
% 2.92/1.00      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
% 2.92/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6,plain,
% 2.92/1.00      ( ~ v2_pre_topc(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0)
% 2.92/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.92/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1618,plain,
% 2.92/1.00      ( v2_pre_topc(X0) != iProver_top
% 2.92/1.00      | l1_pre_topc(X0) != iProver_top
% 2.92/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3346,plain,
% 2.92/1.00      ( v2_pre_topc(sK3) != iProver_top
% 2.92/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.92/1.00      | v1_pre_topc(sK4) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_22,c_1618]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_34,negated_conjecture,
% 2.92/1.00      ( v2_pre_topc(sK1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_37,plain,
% 2.92/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_33,negated_conjecture,
% 2.92/1.00      ( l1_pre_topc(sK1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_38,plain,
% 2.92/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_28,negated_conjecture,
% 2.92/1.00      ( m1_pre_topc(sK3,sK1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_43,plain,
% 2.92/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2,plain,
% 2.92/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | v2_pre_topc(X0)
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2257,plain,
% 2.92/1.00      ( ~ m1_pre_topc(sK3,X0)
% 2.92/1.00      | ~ v2_pre_topc(X0)
% 2.92/1.00      | v2_pre_topc(sK3)
% 2.92/1.00      | ~ l1_pre_topc(X0) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2767,plain,
% 2.92/1.00      ( ~ m1_pre_topc(sK3,sK1)
% 2.92/1.00      | ~ v2_pre_topc(sK1)
% 2.92/1.00      | v2_pre_topc(sK3)
% 2.92/1.00      | ~ l1_pre_topc(sK1) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2257]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2768,plain,
% 2.92/1.00      ( m1_pre_topc(sK3,sK1) != iProver_top
% 2.92/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.92/1.00      | v2_pre_topc(sK3) = iProver_top
% 2.92/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2767]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1605,plain,
% 2.92/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3,plain,
% 2.92/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1621,plain,
% 2.92/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.92/1.00      | l1_pre_topc(X1) != iProver_top
% 2.92/1.00      | l1_pre_topc(X0) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2825,plain,
% 2.92/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.92/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_1605,c_1621]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3349,plain,
% 2.92/1.00      ( v1_pre_topc(sK4) = iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3346,c_37,c_38,c_43,c_2768,c_2825]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_26,negated_conjecture,
% 2.92/1.00      ( m1_pre_topc(sK4,sK1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1607,plain,
% 2.92/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2824,plain,
% 2.92/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.92/1.00      | l1_pre_topc(sK4) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_1607,c_1621]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2914,plain,
% 2.92/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_2824,c_38]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1,plain,
% 2.92/1.00      ( ~ l1_pre_topc(X0)
% 2.92/1.00      | ~ v1_pre_topc(X0)
% 2.92/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1623,plain,
% 2.92/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.92/1.00      | l1_pre_topc(X0) != iProver_top
% 2.92/1.00      | v1_pre_topc(X0) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2919,plain,
% 2.92/1.00      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
% 2.92/1.00      | v1_pre_topc(sK4) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2914,c_1623]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3354,plain,
% 2.92/1.00      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_3349,c_2919]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_8,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.92/1.00      | X2 = X1
% 2.92/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1616,plain,
% 2.92/1.00      ( X0 = X1
% 2.92/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.92/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3664,plain,
% 2.92/1.00      ( g1_pre_topc(X0,X1) != sK4
% 2.92/1.00      | u1_struct_0(sK3) = X0
% 2.92/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_22,c_1616]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4,plain,
% 2.92/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.92/1.00      | ~ l1_pre_topc(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2906,plain,
% 2.92/1.00      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.92/1.00      | ~ l1_pre_topc(sK3) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2911,plain,
% 2.92/1.00      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 2.92/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2906]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3666,plain,
% 2.92/1.00      ( g1_pre_topc(X0,X1) != sK4
% 2.92/1.00      | u1_struct_0(sK3) = X0
% 2.92/1.00      | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_22,c_1616]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3792,plain,
% 2.92/1.00      ( u1_struct_0(sK3) = X0 | g1_pre_topc(X0,X1) != sK4 ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3664,c_38,c_2825,c_2911,c_3666]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3793,plain,
% 2.92/1.00      ( g1_pre_topc(X0,X1) != sK4 | u1_struct_0(sK3) = X0 ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_3792]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3798,plain,
% 2.92/1.00      ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_3354,c_3793]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_18,negated_conjecture,
% 2.92/1.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.92/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1611,plain,
% 2.92/1.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_19,negated_conjecture,
% 2.92/1.00      ( sK6 = sK7 ),
% 2.92/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1661,plain,
% 2.92/1.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
% 2.92/1.00      inference(light_normalisation,[status(thm)],[c_1611,c_19]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_12,plain,
% 2.92/1.00      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.92/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ v2_pre_topc(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_0,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_15,plain,
% 2.92/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.92/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.92/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.92/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.92/1.00      | ~ m1_pre_topc(X0,X5)
% 2.92/1.00      | ~ m1_pre_topc(X4,X0)
% 2.92/1.00      | ~ m1_pre_topc(X4,X5)
% 2.92/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.92/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.92/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.92/1.00      | ~ v1_funct_1(X2)
% 2.92/1.00      | v2_struct_0(X5)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X4)
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ v2_pre_topc(X5)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X5)
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_24,negated_conjecture,
% 2.92/1.00      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_456,plain,
% 2.92/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.92/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.92/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.92/1.00      | ~ m1_pre_topc(X0,X5)
% 2.92/1.00      | ~ m1_pre_topc(X4,X0)
% 2.92/1.00      | ~ m1_pre_topc(X4,X5)
% 2.92/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.92/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.92/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.92/1.00      | ~ v1_funct_1(X2)
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X5)
% 2.92/1.00      | v2_struct_0(X4)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X5)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X5)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.92/1.00      | sK5 != X2 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_457,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_pre_topc(X0,X2)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.92/1.00      | ~ v1_funct_1(sK5)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_456]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_25,negated_conjecture,
% 2.92/1.00      ( v1_funct_1(sK5) ),
% 2.92/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_461,plain,
% 2.92/1.00      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_pre_topc(X0,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_457,c_25]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_462,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_pre_topc(X0,X2)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_461]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_14,plain,
% 2.92/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.92/1.00      | ~ m1_pre_topc(X2,X0)
% 2.92/1.00      | m1_pre_topc(X2,X1)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_509,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(forward_subsumption_resolution,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_462,c_14]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_533,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
% 2.92/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | X5 != X6
% 2.92/1.00      | u1_struct_0(X0) != X7
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_509]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_534,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_533]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_755,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_subset_1(X5,u1_struct_0(X6))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | v2_struct_0(X6)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | ~ v2_pre_topc(X6)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X6)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | X3 != X6
% 2.92/1.00      | X4 != X5
% 2.92/1.00      | sK0(X6,X5) != X7
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_534]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_756,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
% 2.92/1.00      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ v2_pre_topc(X3)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X3)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_755]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_11,plain,
% 2.92/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.92/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_667,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.92/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 2.92/1.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X3)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X3)
% 2.92/1.00      | X3 != X1
% 2.92/1.00      | X2 != X0
% 2.92/1.00      | sK0(X3,X2) != X4 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_668,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.92/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_667]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_781,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ v2_pre_topc(X3)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X3)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(forward_subsumption_resolution,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_756,c_668]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_802,plain,
% 2.92/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.92/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.92/1.00      | ~ m1_pre_topc(X3,X2)
% 2.92/1.00      | ~ m1_pre_topc(X0,X3)
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.92/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.92/1.00      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | v2_struct_0(X1)
% 2.92/1.00      | v2_struct_0(X3)
% 2.92/1.00      | v2_struct_0(X2)
% 2.92/1.00      | ~ v2_pre_topc(X1)
% 2.92/1.00      | ~ v2_pre_topc(X2)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | ~ l1_pre_topc(X2)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.92/1.00      inference(forward_subsumption_resolution,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_781,c_3,c_2]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1594,plain,
% 2.92/1.00      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.92/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.92/1.00      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
% 2.92/1.00      | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
% 2.92/1.00      | m1_pre_topc(X1,X3) != iProver_top
% 2.92/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 2.92/1.00      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.92/1.00      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(X1,X4),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 2.92/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 2.92/1.00      | v2_struct_0(X0) = iProver_top
% 2.92/1.00      | v2_struct_0(X2) = iProver_top
% 2.92/1.00      | v2_struct_0(X1) = iProver_top
% 2.92/1.00      | v2_struct_0(X3) = iProver_top
% 2.92/1.00      | v2_pre_topc(X0) != iProver_top
% 2.92/1.00      | v2_pre_topc(X3) != iProver_top
% 2.92/1.00      | l1_pre_topc(X0) != iProver_top
% 2.92/1.00      | l1_pre_topc(X3) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1994,plain,
% 2.92/1.00      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.92/1.00      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.92/1.00      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.92/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.92/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.92/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.92/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.92/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.92/1.00      | v2_struct_0(X1) = iProver_top
% 2.92/1.00      | v2_struct_0(X0) = iProver_top
% 2.92/1.00      | v2_struct_0(X2) = iProver_top
% 2.92/1.00      | v2_struct_0(sK2) = iProver_top
% 2.92/1.00      | v2_pre_topc(X2) != iProver_top
% 2.92/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.92/1.00      | l1_pre_topc(X2) != iProver_top
% 2.92/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.92/1.00      inference(equality_resolution,[status(thm)],[c_1594]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_32,negated_conjecture,
% 2.92/1.00      ( ~ v2_struct_0(sK2) ),
% 2.92/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_39,plain,
% 2.92/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_31,negated_conjecture,
% 2.92/1.00      ( v2_pre_topc(sK2) ),
% 2.92/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_40,plain,
% 2.92/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_30,negated_conjecture,
% 2.92/1.00      ( l1_pre_topc(sK2) ),
% 2.92/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_41,plain,
% 2.92/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2508,plain,
% 2.92/1.00      ( l1_pre_topc(X2) != iProver_top
% 2.92/1.00      | v2_struct_0(X2) = iProver_top
% 2.92/1.00      | v2_struct_0(X0) = iProver_top
% 2.92/1.00      | v2_struct_0(X1) = iProver_top
% 2.92/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.92/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.92/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.92/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.92/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.92/1.00      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.92/1.00      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.92/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.92/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_1994,c_39,c_40,c_41]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2509,plain,
% 2.92/1.00      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.92/1.00      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.92/1.00      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.92/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.92/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.92/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.92/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.92/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.92/1.00      | v2_struct_0(X1) = iProver_top
% 2.92/1.00      | v2_struct_0(X0) = iProver_top
% 2.92/1.00      | v2_struct_0(X2) = iProver_top
% 2.92/1.00      | v2_pre_topc(X2) != iProver_top
% 2.92/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_2508]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2526,plain,
% 2.92/1.00      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.92/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.92/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.92/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.92/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.92/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.92/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.92/1.00      | v2_struct_0(X1) = iProver_top
% 2.92/1.00      | v2_struct_0(X0) = iProver_top
% 2.92/1.00      | v2_struct_0(sK4) = iProver_top
% 2.92/1.00      | v2_pre_topc(X1) != iProver_top
% 2.92/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.92/1.00      inference(equality_resolution,[status(thm)],[c_2509]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_27,negated_conjecture,
% 2.92/1.00      ( ~ v2_struct_0(sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_44,plain,
% 2.92/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_23,negated_conjecture,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.92/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_48,plain,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3151,plain,
% 2.92/1.00      ( v2_struct_0(X0) = iProver_top
% 2.92/1.00      | v2_struct_0(X1) = iProver_top
% 2.92/1.00      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.92/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.92/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.92/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.92/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.92/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.92/1.00      | v2_pre_topc(X1) != iProver_top
% 2.92/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_2526,c_44,c_48]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3152,plain,
% 2.92/1.00      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.92/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.92/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.92/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.92/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.92/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.92/1.00      | v2_struct_0(X1) = iProver_top
% 2.92/1.00      | v2_struct_0(X0) = iProver_top
% 2.92/1.00      | v2_pre_topc(X1) != iProver_top
% 2.92/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_3151]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3168,plain,
% 2.92/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 2.92/1.00      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.92/1.00      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.92/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.92/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | v2_struct_0(sK1) = iProver_top
% 2.92/1.00      | v2_struct_0(sK3) = iProver_top
% 2.92/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.92/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_1661,c_3152]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_35,negated_conjecture,
% 2.92/1.00      ( ~ v2_struct_0(sK1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_36,plain,
% 2.92/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_29,negated_conjecture,
% 2.92/1.00      ( ~ v2_struct_0(sK3) ),
% 2.92/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_42,plain,
% 2.92/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_45,plain,
% 2.92/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_21,negated_conjecture,
% 2.92/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_49,plain,
% 2.92/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_17,negated_conjecture,
% 2.92/1.00      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
% 2.92/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_52,plain,
% 2.92/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_20,negated_conjecture,
% 2.92/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1610,plain,
% 2.92/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1648,plain,
% 2.92/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.92/1.00      inference(light_normalisation,[status(thm)],[c_1610,c_19]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3171,plain,
% 2.92/1.00      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3168,c_36,c_37,c_38,c_42,c_45,c_49,c_52,c_1648]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4114,plain,
% 2.92/1.00      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.92/1.00      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.92/1.00      inference(demodulation,[status(thm)],[c_3798,c_3171]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_13,plain,
% 2.92/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1614,plain,
% 2.92/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 2.92/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_10,plain,
% 2.92/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.92/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.92/1.00      | ~ l1_pre_topc(X0)
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_186,plain,
% 2.92/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.92/1.00      | ~ m1_pre_topc(X0,X1)
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_10,c_3]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_187,plain,
% 2.92/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.92/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.92/1.00      | ~ l1_pre_topc(X1) ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_186]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1597,plain,
% 2.92/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.92/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.92/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3225,plain,
% 2.92/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.92/1.00      | m1_pre_topc(X0,sK4) = iProver_top
% 2.92/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_22,c_1597]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3237,plain,
% 2.92/1.00      ( m1_pre_topc(X0,sK4) = iProver_top
% 2.92/1.00      | m1_pre_topc(X0,sK3) != iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3225,c_38,c_2825]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3238,plain,
% 2.92/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.92/1.00      | m1_pre_topc(X0,sK4) = iProver_top ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_3237]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3245,plain,
% 2.92/1.00      ( m1_pre_topc(sK3,sK4) = iProver_top
% 2.92/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_1614,c_3238]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2271,plain,
% 2.92/1.00      ( ~ m1_pre_topc(sK4,X0)
% 2.92/1.00      | ~ v2_pre_topc(X0)
% 2.92/1.00      | v2_pre_topc(sK4)
% 2.92/1.00      | ~ l1_pre_topc(X0) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2794,plain,
% 2.92/1.00      ( ~ m1_pre_topc(sK4,sK1)
% 2.92/1.00      | ~ v2_pre_topc(sK1)
% 2.92/1.00      | v2_pre_topc(sK4)
% 2.92/1.00      | ~ l1_pre_topc(sK1) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2271]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2795,plain,
% 2.92/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.92/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.92/1.00      | v2_pre_topc(sK4) = iProver_top
% 2.92/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1937,plain,
% 2.92/1.00      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.92/1.00      | v2_struct_0(sK4)
% 2.92/1.00      | ~ v2_pre_topc(sK4)
% 2.92/1.00      | ~ l1_pre_topc(sK4) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_668]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1938,plain,
% 2.92/1.00      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.92/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | v2_struct_0(sK4) = iProver_top
% 2.92/1.00      | v2_pre_topc(sK4) != iProver_top
% 2.92/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(contradiction,plain,
% 2.92/1.00      ( $false ),
% 2.92/1.00      inference(minisat,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_4114,c_3245,c_2825,c_2824,c_2795,c_1938,c_49,c_45,
% 2.92/1.00                 c_44,c_38,c_37]) ).
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  ------                               Statistics
% 2.92/1.00  
% 2.92/1.00  ------ General
% 2.92/1.00  
% 2.92/1.00  abstr_ref_over_cycles:                  0
% 2.92/1.00  abstr_ref_under_cycles:                 0
% 2.92/1.00  gc_basic_clause_elim:                   0
% 2.92/1.00  forced_gc_time:                         0
% 2.92/1.00  parsing_time:                           0.016
% 2.92/1.00  unif_index_cands_time:                  0.
% 2.92/1.00  unif_index_add_time:                    0.
% 2.92/1.00  orderings_time:                         0.
% 2.92/1.00  out_proof_time:                         0.015
% 2.92/1.00  total_time:                             0.198
% 2.92/1.00  num_of_symbols:                         56
% 2.92/1.00  num_of_terms:                           3957
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing
% 2.92/1.00  
% 2.92/1.00  num_of_splits:                          0
% 2.92/1.00  num_of_split_atoms:                     0
% 2.92/1.00  num_of_reused_defs:                     0
% 2.92/1.00  num_eq_ax_congr_red:                    9
% 2.92/1.00  num_of_sem_filtered_clauses:            1
% 2.92/1.00  num_of_subtypes:                        0
% 2.92/1.00  monotx_restored_types:                  0
% 2.92/1.00  sat_num_of_epr_types:                   0
% 2.92/1.00  sat_num_of_non_cyclic_types:            0
% 2.92/1.00  sat_guarded_non_collapsed_types:        0
% 2.92/1.00  num_pure_diseq_elim:                    0
% 2.92/1.00  simp_replaced_by:                       0
% 2.92/1.00  res_preprocessed:                       163
% 2.92/1.00  prep_upred:                             0
% 2.92/1.00  prep_unflattend:                        17
% 2.92/1.00  smt_new_axioms:                         0
% 2.92/1.00  pred_elim_cands:                        7
% 2.92/1.00  pred_elim:                              4
% 2.92/1.00  pred_elim_cl:                           4
% 2.92/1.00  pred_elim_cycles:                       7
% 2.92/1.00  merged_defs:                            0
% 2.92/1.00  merged_defs_ncl:                        0
% 2.92/1.00  bin_hyper_res:                          0
% 2.92/1.00  prep_cycles:                            4
% 2.92/1.00  pred_elim_time:                         0.017
% 2.92/1.00  splitting_time:                         0.
% 2.92/1.00  sem_filter_time:                        0.
% 2.92/1.00  monotx_time:                            0.
% 2.92/1.00  subtype_inf_time:                       0.
% 2.92/1.00  
% 2.92/1.00  ------ Problem properties
% 2.92/1.00  
% 2.92/1.00  clauses:                                32
% 2.92/1.00  conjectures:                            17
% 2.92/1.00  epr:                                    16
% 2.92/1.00  horn:                                   29
% 2.92/1.00  ground:                                 17
% 2.92/1.00  unary:                                  17
% 2.92/1.00  binary:                                 2
% 2.92/1.00  lits:                                   96
% 2.92/1.00  lits_eq:                                11
% 2.92/1.00  fd_pure:                                0
% 2.92/1.00  fd_pseudo:                              0
% 2.92/1.00  fd_cond:                                0
% 2.92/1.00  fd_pseudo_cond:                         2
% 2.92/1.00  ac_symbols:                             0
% 2.92/1.00  
% 2.92/1.00  ------ Propositional Solver
% 2.92/1.00  
% 2.92/1.00  prop_solver_calls:                      27
% 2.92/1.00  prop_fast_solver_calls:                 1435
% 2.92/1.00  smt_solver_calls:                       0
% 2.92/1.00  smt_fast_solver_calls:                  0
% 2.92/1.00  prop_num_of_clauses:                    1257
% 2.92/1.00  prop_preprocess_simplified:             4996
% 2.92/1.00  prop_fo_subsumed:                       31
% 2.92/1.00  prop_solver_time:                       0.
% 2.92/1.00  smt_solver_time:                        0.
% 2.92/1.00  smt_fast_solver_time:                   0.
% 2.92/1.00  prop_fast_solver_time:                  0.
% 2.92/1.00  prop_unsat_core_time:                   0.
% 2.92/1.00  
% 2.92/1.00  ------ QBF
% 2.92/1.00  
% 2.92/1.00  qbf_q_res:                              0
% 2.92/1.00  qbf_num_tautologies:                    0
% 2.92/1.00  qbf_prep_cycles:                        0
% 2.92/1.00  
% 2.92/1.00  ------ BMC1
% 2.92/1.00  
% 2.92/1.00  bmc1_current_bound:                     -1
% 2.92/1.00  bmc1_last_solved_bound:                 -1
% 2.92/1.00  bmc1_unsat_core_size:                   -1
% 2.92/1.00  bmc1_unsat_core_parents_size:           -1
% 2.92/1.00  bmc1_merge_next_fun:                    0
% 2.92/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation
% 2.92/1.00  
% 2.92/1.00  inst_num_of_clauses:                    376
% 2.92/1.00  inst_num_in_passive:                    104
% 2.92/1.00  inst_num_in_active:                     228
% 2.92/1.00  inst_num_in_unprocessed:                44
% 2.92/1.00  inst_num_of_loops:                      250
% 2.92/1.00  inst_num_of_learning_restarts:          0
% 2.92/1.00  inst_num_moves_active_passive:          19
% 2.92/1.00  inst_lit_activity:                      0
% 2.92/1.00  inst_lit_activity_moves:                0
% 2.92/1.00  inst_num_tautologies:                   0
% 2.92/1.00  inst_num_prop_implied:                  0
% 2.92/1.00  inst_num_existing_simplified:           0
% 2.92/1.00  inst_num_eq_res_simplified:             0
% 2.92/1.00  inst_num_child_elim:                    0
% 2.92/1.00  inst_num_of_dismatching_blockings:      126
% 2.92/1.00  inst_num_of_non_proper_insts:           501
% 2.92/1.00  inst_num_of_duplicates:                 0
% 2.92/1.00  inst_inst_num_from_inst_to_res:         0
% 2.92/1.00  inst_dismatching_checking_time:         0.
% 2.92/1.00  
% 2.92/1.00  ------ Resolution
% 2.92/1.00  
% 2.92/1.00  res_num_of_clauses:                     0
% 2.92/1.00  res_num_in_passive:                     0
% 2.92/1.00  res_num_in_active:                      0
% 2.92/1.00  res_num_of_loops:                       167
% 2.92/1.00  res_forward_subset_subsumed:            43
% 2.92/1.00  res_backward_subset_subsumed:           2
% 2.92/1.00  res_forward_subsumed:                   0
% 2.92/1.00  res_backward_subsumed:                  0
% 2.92/1.00  res_forward_subsumption_resolution:     8
% 2.92/1.00  res_backward_subsumption_resolution:    0
% 2.92/1.00  res_clause_to_clause_subsumption:       239
% 2.92/1.00  res_orphan_elimination:                 0
% 2.92/1.00  res_tautology_del:                      60
% 2.92/1.00  res_num_eq_res_simplified:              0
% 2.92/1.00  res_num_sel_changes:                    0
% 2.92/1.00  res_moves_from_active_to_pass:          0
% 2.92/1.00  
% 2.92/1.00  ------ Superposition
% 2.92/1.00  
% 2.92/1.00  sup_time_total:                         0.
% 2.92/1.00  sup_time_generating:                    0.
% 2.92/1.00  sup_time_sim_full:                      0.
% 2.92/1.00  sup_time_sim_immed:                     0.
% 2.92/1.00  
% 2.92/1.00  sup_num_of_clauses:                     56
% 2.92/1.00  sup_num_in_active:                      43
% 2.92/1.00  sup_num_in_passive:                     13
% 2.92/1.00  sup_num_of_loops:                       49
% 2.92/1.00  sup_fw_superposition:                   32
% 2.92/1.00  sup_bw_superposition:                   9
% 2.92/1.00  sup_immediate_simplified:               6
% 2.92/1.00  sup_given_eliminated:                   2
% 2.92/1.00  comparisons_done:                       0
% 2.92/1.00  comparisons_avoided:                    0
% 2.92/1.00  
% 2.92/1.00  ------ Simplifications
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  sim_fw_subset_subsumed:                 5
% 2.92/1.00  sim_bw_subset_subsumed:                 7
% 2.92/1.00  sim_fw_subsumed:                        0
% 2.92/1.00  sim_bw_subsumed:                        0
% 2.92/1.00  sim_fw_subsumption_res:                 0
% 2.92/1.00  sim_bw_subsumption_res:                 0
% 2.92/1.00  sim_tautology_del:                      6
% 2.92/1.00  sim_eq_tautology_del:                   4
% 2.92/1.00  sim_eq_res_simp:                        0
% 2.92/1.00  sim_fw_demodulated:                     0
% 2.92/1.00  sim_bw_demodulated:                     5
% 2.92/1.00  sim_light_normalised:                   3
% 2.92/1.00  sim_joinable_taut:                      0
% 2.92/1.00  sim_joinable_simp:                      0
% 2.92/1.00  sim_ac_normalised:                      0
% 2.92/1.00  sim_smt_subsumption:                    0
% 2.92/1.00  
%------------------------------------------------------------------------------
